/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_context.cpp

Abstract:

    Bounded PREDABST (symbolic simulation using Z3) context.

Author:

    Modified by Andrey Rybalchenko (rybal) 2014-3-7.

Revision History:

--*/
#include "predabst_util.h"
#include "farkas_util.h"
#include "predabst_context.h"
#include "dl_context.h"
#include "unifier.h"
#include "var_subst.h"
#include "substitution.h"
#include "smt_kernel.h"
#include "dl_transforms.h"

namespace datalog {

    struct refine_cand_info {
        obj_map<func_decl, vector<expr_ref_vector> > m_allrels_info;
        vector<expr_ref_vector> m_empty;

        void insert(func_decl* fdecl, expr_ref_vector const& args) {
            if (!m_allrels_info.contains(fdecl)) {
                m_allrels_info.insert(fdecl, m_empty);
            }
            m_allrels_info[fdecl].push_back(args);
        }

        vector<expr_ref_vector> const& get(func_decl* fdecl) const {
            if (m_allrels_info.contains(fdecl)) {
                return m_allrels_info[fdecl];
            }
            else {
                return m_empty;
            }
        }
    };

    class predabst::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsumed;
        };

        class scoped_push {
            smt::kernel& s;
        public:
            scoped_push(smt::kernel& s) : s(s) { s.push(); }
            ~scoped_push() { s.pop(1); }
        };

        typedef vector<bool> cube_t;
        typedef vector<unsigned> node_vector;
        typedef uint_set node_set;
        //typedef uint_set rule_set; // rule_set has another meaning; use node_id_set/rule_id_set?

        struct func_decl_info {
            expr_ref_vector m_vars;
            expr_ref_vector m_preds;
            uint_set        m_rules;
            node_set        m_max_reach_nodes;
            bool            m_is_output_predicate;
            bool            m_is_wf_predicate;
            func_decl_info(expr_ref_vector const& vars, bool is_output_predicate, bool is_wf_predicate) :
                m_vars(vars),
                m_preds(vars.m()),
                m_is_output_predicate(is_output_predicate),
                m_is_wf_predicate(is_wf_predicate) {}
        };

        struct rule_info {
            func_decl*              m_func_decl;
            rule*                   m_rule;
            unsigned                m_template_id;
            expr_ref                m_body;
            expr_ref_vector         m_head_preds;
            vector<expr_ref_vector> m_body_preds;
            rule_info(func_decl* func_decl, rule* rule, unsigned template_id, ast_manager& m) :
                m_func_decl(func_decl),
                m_rule(rule),
                m_template_id(template_id),
                m_body(m),
                m_head_preds(m) {}
        };

        struct node_info {
            func_decl*  m_func_decl;
            cube_t      m_cube;
            unsigned    m_parent_rule;
            node_vector m_parent_nodes;
            node_info(func_decl* func_decl, cube_t const& cube, unsigned parent_rule, node_vector const& parent_nodes) :
                m_func_decl(func_decl),
                m_cube(cube),
                m_parent_rule(parent_rule),
                m_parent_nodes(parent_nodes) {}
        };

        struct core_tree_node {
            unsigned         m_node_id;
            vector<unsigned> m_names;
            core_tree_node(unsigned node_id) :
                m_node_id(node_id) {}
        };

        typedef std::map<unsigned, core_tree_node> core_tree;

        static const unsigned NON_NODE = UINT_MAX;

        context&               m_ctx;         // main context where (fixedpoint) constraints are stored.
        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        rule_manager&          rm;            // context with utilities for fixedpoint rules.
        smt_params             m_fparams;     // parameters specific to smt solving
        smt::kernel            m_solver;      // basic SMT solver class
        var_subst              m_var_subst;   // substitution object. It gets updated and reset.
        volatile bool          m_cancel;      // Boolean flag to track external cancelation.
        stats                  m_stats;       // statistics information specific to the predabst module.

        rel_template_suit                   m_template;
        func_decl_ref_vector                m_func_decls;
        obj_map<func_decl, func_decl_info*> m_func_decl2info;
        vector<rule_info>                   m_rule2info;
        vector<node_info>                   m_node2info;
        node_set                            m_node_worklist;

        typedef enum { reached_query, not_wf } acr_error_kind;

        struct acr_error {
            unsigned       m_node;
            acr_error_kind m_kind;
            acr_error(unsigned node, acr_error_kind kind) :
                m_node(node),
                m_kind(kind) {}
        };

        struct core_tree_info {
            unsigned            m_root_name;
            expr_ref_vector     m_root_args;
            unsigned            m_last_name;
            unsigned            m_pos;
            core_tree           m_core;
            core_tree_info(ast_manager& m) :
                m_root_args(m) {}
            core_tree_info(unsigned root_name, expr_ref_vector const& root_args, unsigned last_name, unsigned pos, core_tree const& core) :
                m_root_name(root_name),
                m_root_args(root_args),
                m_last_name(last_name),
                m_pos(pos),
                m_core(core) {}
        };

    public:
        imp(context& ctx) :
            m_ctx(ctx),
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_solver(m, m_fparams),
            m_var_subst(m, false),
            m_cancel(false),
            m_func_decls(m),
            m_template(m) {

            m_fparams.m_mbqi = false;
            m_fparams.m_soft_timeout = 1000;
        }

        ~imp() {
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin(),
                end = m_func_decl2info.end(); it != end; ++it) {
                dealloc(it->m_value);
            }
        }

        lbool query(expr* query) {
            m_ctx.ensure_opened();
            rule_set& rules = m_ctx.get_rules();
            rm.mk_query(query, rules);

            find_all_func_decls(rules);

            // Some of the rules are actually declarations of predicate lists,
            // templates and extra constraints on templates.  Find these, and
            // remove them from the rule set.  Note that we must process the
            // extra template constraints before the templates, in order that we
            // know how many extra arguments each template has.
            process_special_rules(rules, is_predicate_list, &imp::collect_predicate_list);
            process_special_rules(rules, is_template_extra, &imp::collect_template_extra);
            process_special_rules(rules, is_template, &imp::collect_template);

            find_rule_uses(rules);

            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                m_rule2info.push_back(rule_info(r->get_decl(), r, 0, m));
            }
            for (unsigned i = 0; i < m_template.get_templates().size(); ++i) {
                m_rule2info.push_back(rule_info(m_template.get_templates().get(i).m_head->get_decl(), nullptr, i, m));
            }

            return abstract_check_refine();
        }

        void cancel() {
            m_cancel = true;
            m_solver.cancel();
        }

        void cleanup() {
            m_cancel = false;
            // TBD hmm?
            m_solver.reset_cancel();
        }

        void reset_statistics() {
            m_stats.reset();
        }

        void collect_statistics(statistics& st) const {
            // TBD hmm?
        }

        void display_certificate(std::ostream& out) const {
            // TBD hmm?
            STRACE("predabst", tout << "inside display_certificate\n";);
            expr_ref ans = get_answer();
            out << mk_pp(ans, m) << "\n";
        }

        expr_ref get_answer() const {
            // TBD hmm?
            return expr_ref(m.mk_true(), m);
        }

        model_ref get_model() const {
            model_ref md = alloc(model, m);
            for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                func_decl* fdecl = m_func_decls[i];
                if (!m_func_decl2info[fdecl]->m_is_output_predicate) {
                    // output predicates are ignored; other predicates are concretized
                    node_set const& nodes = m_func_decl2info[fdecl]->m_max_reach_nodes;
                    expr_ref_vector const& preds = m_func_decl2info[fdecl]->m_preds;
                    expr_ref_vector disj(m);
                    for (node_set::iterator it_node = nodes.begin(),
                        end_node = nodes.end(); it_node != end_node;
                        ++it_node) {
                        cube_t const& cube = m_node2info[*it_node].m_cube;
                        disj.push_back(cube_to_formula(cube, preds));
                    }
                    register_decl(md, fdecl, mk_disj(disj));
                }
            }
            return md;
        }

    private:

        // Apply a substitution vector to an expression, returning the result.
        expr_ref apply_subst(expr* expr, expr_ref_vector const& subst) {
            expr_ref expr2(m);
            m_var_subst(expr, subst.size(), subst.c_ptr(), expr2);
            return expr2;
        }

        // Apply a substitution vector to an application expression, returning the result.
        app_ref apply_subst(app* app, expr_ref_vector const& subst) {
            expr_ref expr2(m);
            m_var_subst(app, subst.size(), subst.c_ptr(), expr2);
            return app_ref(to_app(expr2), m);
        }

        // Apply a substitution vector to each expression in a vector of
        // expressions, returning the result.
        expr_ref_vector apply_subst(expr_ref_vector const& exprs, expr_ref_vector const& subst) {
            expr_ref_vector exprs2(m);
            exprs2.reserve(exprs.size());
            for (unsigned i = 0; i < exprs.size(); ++i) {
                exprs2[i] = apply_subst(exprs[i], subst);
            }
            return exprs2;
        }

        // Returns a substitution vector that maps each variable in vars to the
        // corresponding expression in exprs.
        expr_ref_vector build_subst(unsigned n, expr* const* vars, expr* const* exprs) const {
            expr_ref_vector inst(m);
            inst.reserve(n); // note that this is not necessarily the final size of inst
            for (unsigned i = 0; i < n; ++i) {
                CASSERT("predabst", is_var(vars[i]));
                unsigned idx = to_var(vars[i])->get_idx();
                if (idx >= inst.size()) {
                    inst.resize(idx + 1);
                }
                CASSERT("predabst", !inst.get(idx));
                inst[idx] = exprs[i];
            }
            return inst;
        }

        expr_ref_vector build_subst(expr* const* vars, expr_ref_vector const& exprs) const {
            return build_subst(exprs.size(), vars, exprs.c_ptr());
        }

        expr_ref_vector build_subst(expr_ref_vector const& vars, expr* const* exprs) const {
            return build_subst(vars.size(), vars.c_ptr(), exprs);
        }

        expr_ref_vector build_subst(expr_ref_vector const& vars, expr_ref_vector const& exprs) const {
            CASSERT("predabst", vars.size() == exprs.size());
            return build_subst(vars.size(), vars.c_ptr(), exprs.c_ptr());
        }

        // Returns a vector of fresh constants of the right type to be the first n arguments to fdecl.
        expr_ref_vector get_fresh_args(func_decl* fdecl, char const* prefix, unsigned n) const {
            expr_ref_vector head_args(m);
            head_args.reserve(n);
            for (unsigned i = 0; i < n; ++i) {
                head_args[i] = m.mk_fresh_const(prefix, fdecl->get_domain(i));
            }
            return head_args;
        }

        // Returns a vector of fresh constants of the right type to be arguments to fdecl.
        expr_ref_vector get_fresh_args(func_decl* fdecl, char const* prefix) const {
            return get_fresh_args(fdecl, prefix, fdecl->get_arity());
        }

        // Returns a vector of variables of the right type to be arguments to fdecl.
        expr_ref_vector get_arg_vars(func_decl* fdecl) const {
            expr_ref_vector arg_vars(m);
            arg_vars.reserve(fdecl->get_arity());
            for (unsigned i = 0; i < fdecl->get_arity(); ++i) {
                arg_vars[i] = m.mk_var(i, fdecl->get_domain(i)); // >>> do I need to construct a fresh variable name?
            }
            return arg_vars;
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) covering all the variables used by r, which maps the variables
        // used as head arguments to hvars, and maps all variables that do not
        // appear in the head to fresh contants.
        // >>> Seems like this ought to be able to be written as a combination of build_subst and get_subst_vect_fresh.
        expr_ref_vector get_subst_vect(rule const* r, expr_ref_vector const& hvars, char const* prefix) const {
            CASSERT("predabst", hvars.size() == r->get_decl()->get_arity());

            used_vars used;
            // The following is a clone of r->get_used_vars(&used), which is unfortunately inaccessible.
            used.process(r->get_head());
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                used.process(r->get_tail(i));
            }

            expr_ref_vector rule_subst(m);
            rule_subst.reserve(used.get_max_found_var_idx_plus_1());

            for (unsigned i = 0; i < r->get_decl()->get_arity(); ++i) {
                if (is_var(r->get_head()->get_arg(i))) {
                    unsigned idx = to_var(r->get_head()->get_arg(i))->get_idx();
                    CASSERT("predabst", idx < rule_subst.size());
                    rule_subst[idx] = hvars.get(i);
                }
                else {
                    STRACE("predabst", tout << "Need to unify non-variable " << mk_pp(r->get_head()->get_arg(i), m) << " with " << mk_pp(hvars.get(i), m) << " -- help!\n";);
                    CASSERT("predabst", false);
                    // >>> not clear what we have to do in this case: might be OK if r->get_head()->get_arg(i) and hvargs.get(i) are syntactically equal, but I this is not (always) the case
                }
            }

            for (unsigned i = 0; i < used.get_max_found_var_idx_plus_1(); ++i) {
                if (!rule_subst.get(i)) {
                    sort* s = used.get(i);
                    if (s) {
                        app *c = m.mk_fresh_const(prefix, s);
                        STRACE("predabst", tout << "    var " << i << " -> " << mk_pp(c, m) << " (type " << mk_pp(s, m) << ")\n";);
                        rule_subst[i] = c;
                    }
                }
            }

            return rule_subst;
        }

        // Returns a substitution vector mapping each variable used in r to a
        // fresh constant.
        expr_ref_vector get_subst_vect_free(rule const* r, char const* prefix) const {
            used_vars used;
            // The following is a clone of r->get_used_vars(&used), which is unfortunately inaccessible.
            used.process(r->get_head());
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                used.process(r->get_tail(i));
            }

            expr_ref_vector rule_subst(m);
            rule_subst.reserve(used.get_max_found_var_idx_plus_1());
            for (unsigned i = 0; i < used.get_max_found_var_idx_plus_1(); ++i) {
                sort* s = used.get(i);
                if (s) {
                    app *c = m.mk_fresh_const(prefix, s);
                    STRACE("predabst", tout << "    var " << i << " -> " << mk_pp(c, m) << " (type " << mk_pp(s, m) << ")\n";);
                    rule_subst[i] = c;
                }
            }

            return rule_subst;
        }

        // Returns whether c1 implies c2, or in other words, whether the set
        // represented by c1 is a (non-strict) subset of that represented by c2.
        static bool cube_leq(cube_t const& c1, cube_t const& c2) {
            CASSERT("predabst", c1.size() == c2.size());
            unsigned size = c1.size();
            for (unsigned i = 0; i < size; ++i) {
                if (c2[i] && !c1[i]) {
                    return false;
                }
            }
            // This algorithm is sufficient because cubes are not arbitrary
            // subsets of the predicate list: if a predicate in the list is
            // implied by the other predicates in the cube, then it must also be
            // in the cube.
            return true;
        }

        expr_ref cube_to_formula(cube_t const& cube, expr_ref_vector const& preds) const {
            expr_ref_vector es(m);
            for (unsigned i = 0; i < cube.size(); ++i) {
                if (cube[i]) {
                    es.push_back(preds[i]);
                }
            }
            return mk_conj(es);
        }

        static bool is_regular_rule(rule const* r) {
            return !is_predicate_list(r) && !is_template_extra(r) && !is_template(r);
        }

        void find_all_func_decls(rule_set const& rules) {
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                if (is_regular_rule(r)) {
                    for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                        process_func_decl(rules, r->get_decl(j));
                    }
                    process_func_decl(rules, r->get_decl());
                }
            }
        }

        void process_func_decl(rule_set const& rules, func_decl *fdecl) {
            if (!m_func_decl2info.contains(fdecl)) {
                m_func_decls.push_back(fdecl);
                expr_ref_vector vars = get_arg_vars(fdecl);
                m_func_decl2info.insert(fdecl, alloc(func_decl_info, vars, rules.is_output_predicate(fdecl), is_wf_predicate(fdecl)));
            }
        }

        bool is_wf_predicate(func_decl const* pred) const {
            return pred->get_name() == "__wf__";
        }

        void process_special_rules(rule_set& rules, bool(*p)(rule const*), void (imp::*f)(rule const*)) {
            ptr_vector<rule> to_delete;
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                if (p(r)) {
                    (this->*f)(r);
                    to_delete.push_back(r);
                }
            }

            for (unsigned i = 0; i < to_delete.size(); ++i) {
                rules.del_rule(to_delete[i]);
            }
        }

        static bool is_predicate_list(rule const* r) {
            return r->get_decl()->get_name().str().substr(0, 8) == "__pred__";
        }

        void collect_predicate_list(rule const* r) {
            CASSERT("predabst", is_predicate_list(r));
            // r is a rule of the form:
            //   p1 AND ... AND pN => __pred__SUFFIX
            // Treat p1...pN as initial predicates for query symbol SUFFIX.
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            STRACE("predabst", tout << "Found predicate list for query symbol " << suffix << "("; print_expr_ref_vector(tout, expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()), false); tout << ")\n";);

            func_decl* suffix_decl = m.mk_func_decl(
                suffix,
                head_decl->get_arity(),
                head_decl->get_domain(),
                head_decl->get_range());
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found predicate list for non-existent query symbol " << suffix << "\n";);
                throw default_exception("found predicate list for non-existent query symbol " + suffix.str());
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: predicate list for " << suffix << " has an uninterpreted tail\n";);
                throw default_exception("predicate list for " + suffix.str() + " has an uninterpreted tail");
            }

            // Add p1..pN to m_func_decl2info[SUFFIX].m_preds.
            expr_ref_vector& vars = m_func_decl2info[suffix_decl]->m_vars;
            expr_ref_vector& preds = m_func_decl2info[suffix_decl]->m_preds;
            expr_ref_vector subst = build_subst(r->get_head()->get_args(), vars);
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                STRACE("predabst", tout << "  predicate " << i << ": " << mk_pp(r->get_tail(i), m) << "\n";);
                preds.push_back(apply_subst(r->get_tail(i), subst));
            }
        }

        static bool is_template_extra(rule const* r) {
            return r->get_decl()->get_name() == "__temp__extra__";
        }

        void collect_template_extra(rule const* r) {
            CASSERT("predabst", is_template_extra(r));
            // r is a rule of the form:
            //  ??? => __temp__extra__
            // Treat ??? as an extra template constraint.
            func_decl* head_decl = r->get_decl();
            STRACE("predabst", tout << "Found extra template constraint with " << head_decl->get_arity() << "parameters\n";);

            if (m_template.get_params().size() > 0) {
                STRACE("predabst", tout << "Error: found multiple extra template constraints\n";);
                throw default_exception("found multiple extra template constraints");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: extra template constraint has an uninterpreted tail";);
                throw default_exception("extra template constraint has an uninterpreted tail");
            }

            if (r->get_tail_size() != 1) {
                STRACE("predabst", tout << "Error: extra template constraint tail size is " << r->get_tail_size() << " but should be 1\n";);
                throw default_exception("extra template constraint has tail of length != 1");
            }

            // Replace the variables corresponding to the extra template parameters with fresh constants.
            expr_ref_vector extra_params = get_fresh_args(r->get_decl(), "b");
            expr_ref_vector extra_subst = build_subst(r->get_head()->get_args(), extra_params);
            app_ref extras = apply_subst(r->get_tail(0), extra_subst);
            STRACE("predabst", tout << "  template extra " << mk_pp(extras, m) << "\n";);
            m_template.process_template_extra(extra_params, expr_ref(extras, m));
        }

        static bool is_template(rule const* r) {
            return r->get_decl()->get_name().str().substr(0, 8) == "__temp__";
        }

        void collect_template(rule const* r) {
            CASSERT("predabst", is_template(r));
            // r is a rule of the form:
            //  ??? => __temp__SUFFIX
            // Treat ??? as a template for query symbol SUFFIX.
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            STRACE("predabst", tout << "Found template for query symbol " << suffix << "\n";);

            expr_ref_vector const& extra_params = m_template.get_params();
            unsigned num_extras = extra_params.size();
            if (head_decl->get_arity() < num_extras) {
                STRACE("predabst", tout << "Error: template for " << suffix << " doesn't have enough parameters for the extra template parameters\n";);
                throw default_exception("template for " + suffix.str() + " has insufficient parameters");
            }

            unsigned new_arity = head_decl->get_arity() - num_extras;
            for (unsigned i = 0; i < num_extras; ++i) {
                if (head_decl->get_domain(new_arity + i) != to_app(extra_params[i])->get_decl()->get_range()) {
                    STRACE("predabst", tout << "Error: extra parameter " << i << " to template for " << suffix << " is of wrong type\n";);
                    throw default_exception("extra parameter to template for " + suffix.str() + " is of wrong type");
                }
            }

            func_decl* suffix_decl = m.mk_func_decl(
                suffix,
                new_arity,
                head_decl->get_domain(),
                head_decl->get_range());
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found template for non-existent query symbol " << suffix << "\n";);
                throw default_exception("found template for non-existent query symbol " + suffix.str());
            }

            if (m_template.get_names().contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found multiple templates for " << suffix << "\n";);
                throw default_exception("found multiple templates for " + suffix.str());
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: template has an uninterpreted tail\n";);
                throw default_exception("template for " + suffix.str() + " has an uninterpreted tail");
            }

            if (r->get_tail_size() != 1) {
                STRACE("predabst", tout << "Error: template tail size is " << r->get_tail_size() << " but should be 1\n";);
                throw default_exception("template for " + suffix.str() + " has tail of length != 1");
            }

            // First, replace the variables corresponding to the extra template parameters with their corresponding constants.
            app* orig_head = m.mk_app(suffix_decl, r->get_head()->get_args());
            expr_ref_vector extra_subst = build_subst(r->get_head()->get_args() + new_arity, extra_params);
            app_ref orig_body = apply_subst(r->get_tail(0), extra_subst);
            STRACE("predabst", tout << "  orig template: " << mk_pp(orig_head, m) << "; " << mk_pp(orig_body, m) << "\n";);

            // Second, additionally replace the variables corresponding to the query parameters with fresh constants.
            expr_ref_vector query_params = get_fresh_args(r->get_decl(), "v", new_arity);
            app* head = m.mk_app(suffix_decl, query_params.c_ptr());
            expr_ref_vector all_params = vector_concat(query_params, extra_params);
            expr_ref_vector all_subst = build_subst(r->get_head()->get_args(), all_params);
            app_ref body = apply_subst(r->get_tail(0), all_subst);
            STRACE("predabst", tout << " template: " << mk_pp(head, m) << "; " << mk_pp(body, m) << "\n";);

            m_template.process_template(suffix_decl, rel_template(orig_head, expr_ref(orig_body, m)), rel_template(head, expr_ref(body, m)));
        }

        void find_rule_uses(rule_set const& rules) {
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                CASSERT("predabst", is_regular_rule(r));
                for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                    m_func_decl2info[r->get_decl(j)]->m_rules.insert(i);
                }
            }
        }

        lbool abstract_check_refine() {
            STRACE("predabst", print_initial_state(tout););

            m_template.init_template_instantiate();

            // The only things that change on subsequent iterations of this loop are
            // the predicate lists
            // (m_func_decl2info::m_preds) and m_template.  The latter can have an
            // effect on the execution of the algorithm via the initial nodes
            // set up by initialize_abs.
            unsigned refine_count = 0;
            while (true) {
                for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                    m_func_decl2info[m_func_decls.get(i)]->m_max_reach_nodes.reset();
                }
                m_node2info.reset();
                m_node_worklist.reset();

                // for each rule: ground body and instantiate predicates for applications
                for (unsigned r_id = 0; !m_cancel && r_id < m_rule2info.size(); ++r_id) {
                    rule* r = m_rule2info[r_id].m_rule;
                    if (r) {
                        instantiate_rule(r, r_id);
                    }
                    else {
                        instantiate_template_rule(m_rule2info[r_id].m_template_id, r_id);
                    }
                }

                STRACE("predabst", print_refinement_state(tout, refine_count););

                try {
                    // initial abstract inference
                    STRACE("predabst", tout << "Performing initial inference\n";);
                    for (unsigned r_id = 0; !m_cancel && r_id < m_rule2info.size(); ++r_id) {
                        if (m_rule2info[r_id].m_body_preds.size() == 0) {
                            initialize_abs(r_id);
                        }
                    }
                    // process worklist
                    unsigned infer_count = 0;
                    while (!m_cancel && !m_node_worklist.empty()) {
                        STRACE("predabst", print_inference_state(tout, refine_count, infer_count););
                        unsigned current_id = *m_node_worklist.begin();
                        m_node_worklist.remove(current_id);
                        inference_step(current_id);
                        infer_count++;
                    }
                    if (m_cancel) {
                        STRACE("predabst", tout << "Cancelled: result is UNKNOWN\n";);
                        return l_undef;
                    }

                    // We managed to find a solution.
                    STRACE("predabst", tout << "Worklist empty: result is SAT\n";);
                    return l_false;
                }
                catch (acr_error const& exc) {
                    // Our attempt to find a solution failed.
                    unsigned node_id = exc.m_node;
                    core_tree_info core_info(m);
                    if (mk_core_tree(node_id, core_info)) {
                        // The result didn't hold up without abstraction.  We
                        // need to refine the predicates and retry.
                        if (!refine_unreachable(core_info)) {
                            STRACE("predabst", tout << "Predicate refinement unsuccessful: result is UNKNOWN\n";);
                            return l_undef;
                        }

                        STRACE("predabst", tout << "Predicate refinement successful: retrying\n";);
                    }
                    else {
                        // The result held up even without abstraction.  Unless
                        // we can refine the templates, we have a proof of
                        // unsatisfiability.
                        bool result;
                        if (exc.m_kind == reached_query) {
                            STRACE("predabst", tout << "Refining templates (reachable)\n";);
                            result = refine_t_reach(node_id);
                        }
                        else {
                            CASSERT("predabst", exc.m_kind == not_wf);
                            STRACE("predabst", tout << "Refining templates (WF)\n";);
                            result = refine_t_wf(node_id);
                        }

                        if (!result) {
                            STRACE("predabst", tout << "Template refinement unsuccessful: result is UNSAT\n";);
                            return l_true;
                        }

                        STRACE("predabst", tout << "Template refinement successful: retrying\n";);
                    }
                }

                refine_count++;
            }
        }

        // Sets up m_rule2info for this iteration of the abstract_check_refine loop.
        void instantiate_rule(rule* r, unsigned r_id) {
            STRACE("predabst", tout << "Instantiating rule " << r_id << "\n";);

            // conjoin constraints in rule body
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref conj(m.mk_and(tsz - usz, r->get_expr_tail() + usz), m);
            STRACE("predabst", tout << "  body (before subst): " << mk_pp(conj, m) << "\n";);

            // apply grounding substitution
            expr_ref_vector rule_subst = get_subst_vect_free(r, "c");
            conj = apply_subst(conj, rule_subst);
            STRACE("predabst", tout << "  body (after subst): " << mk_pp(conj, m) << "\n";);

            // store ground body and instantiations
            rule_info& info = m_rule2info[r_id];
            info.m_body = conj;

            // store instantiation for non-query head
            if (!m_func_decl2info[r->get_decl()]->m_is_output_predicate) {
                expr_ref_vector heads = app_inst_preds(apply_subst(r->get_head(), rule_subst));
                for (unsigned i = 0; i < heads.size(); ++i) {
                    heads[i] = m.mk_not(heads.get(i));
                }
                STRACE("predabst", tout << "  head preds: "; print_expr_ref_vector(tout, heads););
                info.m_head_preds.swap(heads);
            }

            // store instantiation for body applications
            info.m_body_preds.reset();
            for (unsigned i = 0; i < usz; ++i) {
                expr_ref_vector tails = app_inst_preds(apply_subst(r->get_tail(i), rule_subst));
                STRACE("predabst", tout << "  body preds " << i << ": "; print_expr_ref_vector(tout, tails););
                info.m_body_preds.push_back(tails);
            }

        }

        // Sets up m_rule2info for this iteration of the abstract_check_refine loop.
        void instantiate_template_rule(unsigned t_id, unsigned r_id) {
            STRACE("predabst", tout << "Instantiating template " << t_id << " (rule " << r_id << ")\n";);
            rel_template const& instance = m_template.get_template_instances().get(t_id);

            rule_info& info = m_rule2info[r_id];
            info.m_body = instance.m_body;

            CASSERT("predabst", !m_func_decl2info[instance.m_head->get_decl()]->m_is_output_predicate);
            expr_ref_vector heads = app_inst_preds(instance.m_head);
            info.m_head_preds.swap(heads);
        }

        // instantiate each predicate by replacing its free variables with (grounded) arguments of gappl
        expr_ref_vector app_inst_preds(app* gappl) {
            expr_ref_vector const& vars = m_func_decl2info[gappl->get_decl()]->m_vars;
            expr_ref_vector const& preds = m_func_decl2info[gappl->get_decl()]->m_preds;
            // instantiation maps preds variables to head arguments
            expr_ref_vector inst = build_subst(vars, gappl->get_args());
            // preds instantiates to inst_preds
            return apply_subst(preds, inst);
        }

        void initialize_abs(unsigned r_id) {
            cube_t cube;
            if (cart_pred_abst_rule(r_id, cube)) {
                check_node_property(add_node(m_rule2info[r_id].m_func_decl, cube, r_id));
            }
        }

        void inference_step(unsigned node_id) {
            // Find all rules whose body contains the func_decl of the new node.
            func_decl* fdecl = m_node2info[node_id].m_func_decl;
            uint_set const& rules = m_func_decl2info[fdecl]->m_rules;
            STRACE("predabst", tout << "Performing inference from node " << node_id << " using rules " << rules << "\n";);
            for (uint_set::iterator r_id = rules.begin(), r_id_end = rules.end(); r_id != r_id_end; ++r_id) {
                STRACE("predabst-cprod", tout << "Attempting to apply rule " << *r_id << "\n";);
                // Find all positions in the body of this rule at which the
                // func_decl appears.
                rule* r = m_rule2info[*r_id].m_rule;
                uint_set current_poss = get_rule_body_positions(r, fdecl);
                CASSERT("predabst", current_poss.num_elems() != 0);
                for (uint_set::iterator current_pos = current_poss.begin(), current_pos_end = current_poss.end(); current_pos != current_pos_end; ++current_pos) {
                    STRACE("predabst-cprod", tout << "Using this node in position " << *current_pos << "\n";);
                    // Find all possible combinations of nodes that can be used
                    // with this rule, assuming that the new node is used at
                    // this position.
                    vector<node_vector> nodes_set = build_cartesian_product(r, node_id, *current_pos);
                    for (vector<node_vector>::iterator nodes = nodes_set.begin(), nodes_end = nodes_set.end(); nodes != nodes_end; ++nodes) {
                        CASSERT("predabst", nodes->size() == r->get_uninterpreted_tail_size());
                        cube_t cube;
                        if (cart_pred_abst_rule(*r_id, cube, *nodes)) {
                            check_node_property(add_node(r->get_decl(), cube, *r_id, *nodes));
                        }
                    }
                }
            }
        }

        uint_set get_rule_body_positions(rule* r, func_decl* fdecl) {
            // XXX we could precompute this set and store it in m_func_decl2info::m_rules
            uint_set positions;
            for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                if (r->get_decl(i) == fdecl) {
                    positions.insert(i);
                }
            }
            return positions;
        }

        vector<node_vector> build_cartesian_product(rule* r, unsigned node, unsigned current_pos) {
            vector<node_vector> nodes_set;
            nodes_set.push_back(node_vector()); // XXX reserve space in this vector, for efficiency?

            node_set current_pos_singleton;
            current_pos_singleton.insert(node);

            // grow node combinations as cartesian product with nodes at pos
            for (unsigned pos = 0; pos < r->get_uninterpreted_tail_size(); ++pos) {
                node_set& pos_nodes = (current_pos == pos) ? current_pos_singleton : m_func_decl2info[r->get_decl(pos)]->m_max_reach_nodes;
                STRACE("predabst-cprod", tout << "There are " << pos_nodes.num_elems() << " option(s) for position " << pos << "\n";);
                if (pos_nodes.num_elems() == 0) {
                    // The Cartesian product with an empty set is the empty set.
                    nodes_set.reset();
                    break;
                }
                unsigned orig_nodes_set_size = nodes_set.size();
                // First, store the product with the first node in-place.
                node_set::iterator pos_node = pos_nodes.begin();
                for (unsigned nodes_set_offset = 0; nodes_set_offset < orig_nodes_set_size; ++nodes_set_offset) {
                    STRACE("predabst-cprod", tout << "Adding " << *pos_node << " to existing set " << nodes_set[nodes_set_offset] << "\n";);
                    nodes_set[nodes_set_offset].push_back(*pos_node);
                }
                ++pos_node;
                // Then, the product with each of the remaining nodes goes into additional vectors.
                for (node_set::iterator pos_node_end = pos_nodes.end(); pos_node != pos_node_end; ++pos_node) {
                    for (unsigned nodes_set_offset = 0; nodes_set_offset < orig_nodes_set_size; ++nodes_set_offset) {
                        STRACE("predabst-cprod", tout << "Using " << *pos_node << " instead of last element of existing set " << nodes_set[nodes_set_offset] << "\n";);
                        node_vector tmp = nodes_set[nodes_set_offset];
                        tmp.back() = *pos_node;
                        nodes_set.push_back(tmp);
                    }
                }
            }

            return nodes_set;
        }

        // This is implementing the "abstract inference rules" from Figure 2 of "synthesizing software verifiers from proof rules".
        // With no 3rd argument, rule Rinit is applied; otherwise rule Rstep is applied.
        bool cart_pred_abst_rule(unsigned r_id, cube_t& cube, node_vector const& nodes = node_vector()) {
            scoped_push _push1(m_solver);
            m_solver.assert_expr(m_rule2info[r_id].m_body);
            // get instantiated predicates
            vector<expr_ref_vector> const& body_preds_vector = m_rule2info[r_id].m_body_preds;
            CASSERT("predabst", body_preds_vector.size() == nodes.size());
            // load abstract states for nodes
            for (unsigned pos = 0; pos < nodes.size(); ++pos) {
                cube_t& pos_cube = m_node2info[nodes[pos]].m_cube;
                expr_ref_vector const& body_preds = body_preds_vector[pos];
                for (unsigned i = 0; i < body_preds.size(); ++i) {
                    if (pos_cube[i]) {
                        m_solver.assert_expr(body_preds[i]);
                    }
                }
            }
            if (m_solver.check() == l_false) {
                // unsat body
                STRACE("predabst", tout << "Applying rule " << r_id << " to nodes (" << nodes << ") failed\n";);
                return false;
            }
            // collect abstract cube
            expr_ref_vector const& head_preds = m_rule2info[r_id].m_head_preds;
            cube.resize(head_preds.size());
            for (unsigned i = 0; i < head_preds.size(); ++i) {
                scoped_push _push2(m_solver);
                m_solver.assert_expr(head_preds[i]);
                cube[i] = (m_solver.check() == l_false);
            }
            STRACE("predabst", tout << "Applying rule " << r_id << " to nodes (" << nodes << ") succeeded, with cube [" << cube << "]\n";);
            return true;
        }

        void check_node_property(unsigned id) {
            if (id != NON_NODE) {
                if (m_func_decl2info[m_node2info[id].m_func_decl]->m_is_output_predicate) {
                    STRACE("predabst", tout << "Reached query symbol " << m_node2info[id].m_func_decl->get_name() << "\n";);
                    throw acr_error(id, reached_query);
                }
                if (m_func_decl2info[m_node2info[id].m_func_decl]->m_is_wf_predicate) {
                    if (!is_well_founded(id)) {
                        STRACE("predabst", tout << "Formula is not well-founded\n";);
                        throw acr_error(id, not_wf);
                    }
                }
            }
        }

        bool is_well_founded(unsigned id) {
            func_decl* fdecl = m_node2info[id].m_func_decl;
            cube_t cube = m_node2info[id].m_cube;

            expr_ref_vector const& vars = m_func_decl2info[fdecl]->m_vars;
            expr_ref_vector const& preds = m_func_decl2info[fdecl]->m_preds;
            expr_ref expr = cube_to_formula(cube, preds);
            expr_ref_vector args = get_fresh_args(fdecl, "s");
            expr_ref to_rank = apply_subst(expr, build_subst(vars, args));

            expr_ref bound(m);
            expr_ref decrease(m);
            return well_founded(args, to_rank, bound, decrease);
        }

        unsigned add_node(func_decl* sym, cube_t const& cube, unsigned r_id, node_vector const& nodes = node_vector()) {
            // first fixpoint check combined with maximality maintainance
            node_set& sym_nodes = m_func_decl2info[sym]->m_max_reach_nodes;
            node_vector old_lt_nodes;
            for (node_set::iterator it = sym_nodes.begin(), end = sym_nodes.end(); it != end; ++it) {
                cube_t& old_cube = m_node2info[*it].m_cube;
                // if cube implies existing cube then nothing to add
                if (cube_leq(cube, old_cube)) {
                    STRACE("predabst", tout << "New node is subsumed by node " << *it << " with cube [" << old_cube << "]\n";);
                    CASSERT("predabst", old_lt_nodes.size() == 0);
                    return NON_NODE;
                }
                // stronger old cubes will not be considered maximal
                if (cube_leq(old_cube, cube)) {
                    STRACE("predabst", tout << "New node subsumes node " << *it << " with cube [" << old_cube << "]\n";);
                    old_lt_nodes.push_back(*it);
                }
            }
            // (no???) fixpoint reached since didn't return
            // remove subsumed maximal nodes
            for (node_vector::iterator it = old_lt_nodes.begin(), end = old_lt_nodes.end(); it != end; ++it) {
                sym_nodes.remove(*it);
                m_node_worklist.remove(*it); // removing non-existent element is ok
            }
            // no fixpoint reached hence create new node
            unsigned added_id = m_node2info.size();
            sym_nodes.insert(added_id);
            m_node_worklist.insert(added_id);
            m_node2info.push_back(node_info(sym, cube, r_id, nodes));
            STRACE("predabst", tout << "Added node " << added_id << " for " << sym->get_name() << "\n";);
            return added_id;
        }

        bool refine_unreachable(core_tree_info const& core_info) {
            refine_cand_info allrels_info;
            core_clauses clauses = mk_core_clauses(core_info, allrels_info);
            vector<refine_pred_info> interpolants = solve_clauses(clauses, m);
            return refine_preds(allrels_info, interpolants);
        }

        bool refine_t_reach(unsigned node_id) {
            expr_ref cs = mk_leaf(get_fresh_args(m_node2info[node_id].m_func_decl, "l"), node_id);
            expr_ref imp(m.mk_not(cs), m);
            return m_template.constrain_template(imp);
        }

        bool refine_t_wf(unsigned node_id) {
            func_decl* fdecl = m_node2info[node_id].m_func_decl;
            expr_ref_vector args = get_fresh_args(fdecl, "s");
            expr_ref to_wf(m.mk_true(), m);
            refine_cand_info to_refine_cand_info;
            mk_core_tree_wf(args, node_id, to_wf, to_refine_cand_info);
            to_refine_cand_info.insert(fdecl, args);

            expr_ref bound(m);
            expr_ref decrease(m);
            if (well_founded(args, to_wf, bound, decrease)) {
                vector<refine_pred_info> interpolants;
                interpolants.push_back(refine_pred_info(bound, get_all_vars(bound)));
                interpolants.push_back(refine_pred_info(decrease, get_all_vars(decrease)));
                for (unsigned i = 0; i < interpolants.size(); ++i) {
                    STRACE("predabst", tout << "Interpolant " << i << ":"; interpolants.get(i).display(tout););
                }
                return refine_preds(to_refine_cand_info, interpolants);
            }

            expr_ref cs = mk_leaf(args, node_id);
            expr_ref_vector cs_vars(get_all_vars(cs));

            app_ref_vector q_vars(m);
            for (unsigned i = 0; i < cs_vars.size(); ++i) {
                if (!args.contains(cs_vars.get(i))) {
                    q_vars.push_back(to_app(cs_vars.get(i)));
                }
            }

            qe_lite ql1(m);
            ql1(q_vars, cs);
            expr_ref bound_cs(m);
            expr_ref decrease_cs(m);
            well_founded_cs(args, bound_cs, decrease_cs);
            expr_ref to_solve(m.mk_or(m.mk_not(cs), m.mk_and(bound_cs, decrease_cs)), m);
            return m_template.constrain_template(to_solve);
        }

        bool refine_preds(refine_cand_info const& allrels_info, vector<refine_pred_info> const& interpolants) {
            unsigned new_preds_added = 0;
            for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                func_decl *fdecl = m_func_decls.get(i);
                vector<expr_ref_vector> rel_info = allrels_info.get(fdecl);
                for (unsigned j = 0; j < rel_info.size(); ++j) {
                    for (unsigned k = 0; k < interpolants.size(); ++k) {
                        new_preds_added += get_interpolant_pred(fdecl, rel_info.get(j), interpolants.get(k));
                    }
                }
            }
            return (new_preds_added > 0);
        }

        static bool is_args_pred(expr_ref_vector const& args, expr_ref_vector const& vars) {
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (!args.contains(vars.get(i))) {
                    return false;
                }
            }
            return true;
        }

        unsigned get_interpolant_pred(func_decl* fdecl, expr_ref_vector const& args, refine_pred_info const& interpolant) {
            expr_ref_vector const& vars = m_func_decl2info[fdecl]->m_vars;
            expr_ref_vector& preds = m_func_decl2info[fdecl]->m_preds;

            unsigned new_preds_added = 0;
            if (is_args_pred(args, interpolant.m_pred_vars)) {
                expr_ref const& in_pred = interpolant.m_pred;
                expr_ref in_pred2(replace_pred(args, vars, in_pred), m);
                if (!preds.contains(in_pred2)) {
                    STRACE("predabst", tout << "Found new predicate " << mk_pp(in_pred2, m) << " for " << fdecl->get_name() << "\n";);
                    preds.push_back(in_pred2);
                    ++new_preds_added;
                }
                else {
                    STRACE("predabst", tout << "Predicate " << mk_pp(in_pred2, m) << " for " << fdecl->get_name() << " is already present\n";);
                }
            }
            STRACE("predabst", tout << "Found " << new_preds_added << " new predicates for " << fdecl->get_name() << " using "; print_expr_ref_vector(tout, args, false); tout << ", ";  interpolant.display(tout););
            return new_preds_added;
        }

        bool mk_core_tree(unsigned node_id, core_tree_info &core_info) {
            smt_params new_param;
            smt::kernel solver(m, new_param);
            core_tree& core = core_info.m_core;
            unsigned& root_name = core_info.m_root_name;
            expr_ref_vector& root_args = core_info.m_root_args;
            unsigned count = 0;

            struct todo_item {
                unsigned        m_name;
                expr_ref_vector m_hargs;
                unsigned        m_node_id;
                todo_item(unsigned name, expr_ref_vector const& hargs, unsigned node_id) :
                    m_name(name),
                    m_hargs(hargs),
                    m_node_id(node_id) {}
            };
            vector<todo_item> todo;

            root_name = count++;
            root_args.append(get_fresh_args(m_node2info[node_id].m_func_decl, "r"));
            todo.push_back(todo_item(root_name, root_args, node_id));

            while (!todo.empty()) {
                todo_item item = todo.back();
                todo.pop_back();

                unsigned hname = item.m_name;
                expr_ref_vector const& hargs = item.m_hargs;
                unsigned n_id = item.m_node_id;

                core.insert(std::make_pair(hname, core_tree_node(n_id)));
                vector<unsigned>& names = core.at(hname).m_names;

                node_info const& node = m_node2info[n_id];
                rule* r = m_rule2info[node.m_parent_rule].m_rule;
                if (!r) {
                    STRACE("predabst", tout << "mk_core_tree: node " << n_id << "; " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << ") was generated by a template\n";);
                    expr_ref orig_temp_body(m);
                    expr_ref_vector orig_temp_vars(m);
                    bool found = m_template.get_orig_template(node.m_func_decl, orig_temp_body, orig_temp_vars);
                    CASSERT("predabst", found);
                    expr_ref_vector temp_subst = build_subst(orig_temp_vars, hargs); // >>> should we also be substituting the current chosen values for the extra template parameters?
                    orig_temp_body = apply_subst(orig_temp_body, temp_subst);
                    expr_ref_vector inst_body_terms = get_conj_terms(orig_temp_body);
                    for (unsigned i = 0; i < inst_body_terms.size(); ++i) {
                        solver.assert_expr(inst_body_terms.get(i));
                        if (solver.check() == l_false) {
                            core_info.m_last_name = hname;
                            core_info.m_pos = i;
                            return true;
                        }
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_core_tree: node " << n_id << "; " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << ") was generated by a rule application\n";);
                    expr_ref_vector rule_subst = get_subst_vect(r, hargs, "s");
                    unsigned usz = r->get_uninterpreted_tail_size();
                    unsigned tsz = r->get_tail_size();
                    for (unsigned i = usz; i < tsz; ++i) {
                        app_ref as = apply_subst(r->get_tail(i), rule_subst);
                        solver.assert_expr(as);
                        if (solver.check() == l_false) {
                            core_info.m_last_name = hname;
                            core_info.m_pos = i;
                            return true;
                        }
                    }
                    for (unsigned i = 0; i < usz; ++i) { // Each iteration corresponds to an in-arrow to this node.
                        app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                        expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                        unsigned name = count++;
                        names.push_back(name);
                        todo.push_back(todo_item(name, qargs, node.m_parent_nodes.get(i)));
                    }
                }
            }

            return false;
        }

        void mk_core_tree_wf(expr_ref_vector hargs, unsigned n_id, expr_ref& to_wf, refine_cand_info& refine_cand_info_set) {
            STRACE("predabst", tout << "mk_core_tree_wf: node " << n_id << "; " << "("; print_expr_ref_vector(tout, hargs, false); tout << ")\n";);

            struct todo_item {
                expr_ref_vector m_hargs;
                unsigned        m_node_id;
                todo_item(expr_ref_vector const& hargs, unsigned node_id) :
                    m_hargs(hargs),
                    m_node_id(node_id) {}
            };
            vector<todo_item> todo;

            node_info const& node = m_node2info[n_id];
            expr_ref cs(m);
            rule* r = m_rule2info[node.m_parent_rule].m_rule;
            if (!r) {
                STRACE("predabst", tout << "mk_core_tree_wf: node was generated by a template\n";);
                expr_ref orig_temp_body(m);
                expr_ref_vector orig_temp_vars(m);
                bool found = m_template.get_orig_template(node.m_func_decl, orig_temp_body, orig_temp_vars);
                CASSERT("predabst", found);
                expr_ref_vector temp_subst = build_subst(orig_temp_vars, hargs);
                orig_temp_body = apply_subst(orig_temp_body, temp_subst);
                expr_ref inst_body(m);
                m_template.get_modref()->eval(orig_temp_body, inst_body);
                cs = mk_conj(cs, inst_body);
            }
            else {
                STRACE("predabst", tout << "mk_core_tree_wf: node was generated by a rule application\n";);
                expr_ref_vector rule_subst = get_subst_vect(r, hargs, "s");
                unsigned usz = r->get_uninterpreted_tail_size();
                unsigned tsz = r->get_tail_size();
                cs = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
                for (unsigned i = 0; i < usz; ++i) {
                    app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                    expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                    refine_cand_info_set.insert(qs_i->get_decl(), qargs);
                    todo.push_back(todo_item(qargs, node.m_parent_nodes.get(i)));
                }
            }
            to_wf = mk_conj(to_wf, cs);
            for (unsigned i = 0; i < todo.size(); ++i) {
                todo_item const& item = todo.get(i);
                mk_core_tree_wf(item.m_hargs, item.m_node_id, to_wf, refine_cand_info_set);
            }
        }

        // The last parameter builds up information that will ultimately be passed to refine_preds.
        core_clauses mk_core_clauses(core_tree_info const& core_info, refine_cand_info &refine_cand_info_set) {
            core_clauses clauses;

            unsigned root_name = core_info.m_root_name;
            expr_ref_vector const& root_hargs = core_info.m_root_args;
            core_tree const& core = core_info.m_core;
            unsigned last_name = core_info.m_last_name;

            struct todo_item {
                unsigned        m_name;
                expr_ref_vector m_hargs;
                todo_item(unsigned name, expr_ref_vector const& hargs) :
                    m_name(name),
                    m_hargs(hargs) {}
            };
            vector<todo_item> todo;

            todo.push_back(todo_item(root_name, root_hargs));

            bool found_last = false;
            while (!found_last) {
                CASSERT("predabst", !todo.empty());
                todo_item item = todo.back();
                todo.pop_back();

                unsigned hname = item.m_name;
                expr_ref_vector const& hargs = item.m_hargs;
                STRACE("predabst", tout << "mk_core_clauses: " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << ")\n";);

                if (hname == last_name) {
                    found_last = true;
                }

                expr_ref cs(m);
                expr_ref_vector cl_bs(m);

                node_info const& node = m_node2info[core.at(hname).m_node_id];
                vector<unsigned> const& names = core.at(hname).m_names;
                rule* r = m_rule2info[node.m_parent_rule].m_rule;

                if (!r) {
                    if (found_last) {
                        STRACE("predabst", tout << "mk_core_clauses: last node was generated by a template\n";);
                        expr_ref inst_body(m);
                        expr_ref_vector inst_vars(m);
                        bool found = m_template.get_template_instance(node.m_func_decl, inst_body, inst_vars); // >>> why using instance, not orig, here?  why no use of hvars in this branch?
                        CASSERT("predabst", found);
                        expr_ref_vector inst_body_terms = get_conj_terms(inst_body);
                        cs = mk_conj(expr_ref_vector(m, core_info.m_pos + 1, inst_body_terms.c_ptr()));
                    }
                    else {
                        STRACE("predabst", tout << "mk_core_clauses: node was generated by a template\n";);
                        expr_ref orig_temp_body(m);
                        expr_ref_vector orig_temp_vars(m);
                        bool found = m_template.get_orig_template(node.m_func_decl, orig_temp_body, orig_temp_vars);
                        CASSERT("predabst", found);
                        expr_ref_vector temp_subst = build_subst(orig_temp_vars, hargs);
                        orig_temp_body = apply_subst(orig_temp_body, temp_subst);
                        expr_ref inst_body(m);
                        m_template.get_modref()->eval(orig_temp_body, inst_body);
                        cs = inst_body;
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_core_clauses_internal: node was generated by a rule application\n";);
                    expr_ref_vector rule_subst = get_subst_vect(r, hargs, "s");
                    unsigned usz = r->get_uninterpreted_tail_size();
                    unsigned tsz = r->get_tail_size();
                    if (found_last) {
                        cs = apply_subst(mk_conj(expr_ref_vector(m, core_info.m_pos - usz + 1, r->get_expr_tail() + usz)), rule_subst);
                    }
                    else {
                        cs = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
                    }
                    for (unsigned i = 0; i < names.size(); ++i) {
                        app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                        expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                        refine_cand_info_set.insert(qs_i->get_decl(), qargs);
                        cl_bs.push_back(qs_i);
                        todo.push_back(todo_item(names.get(i), qargs));
                    }
                }

                if (hargs.size() > 0 || !m.is_true(cs)) {
                    STRACE("predabst", tout << "Adding core clause " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << "); " << mk_pp(cs, m) << "; "; print_expr_ref_vector(tout, cl_bs););
                    clauses.insert(std::make_pair(hname, std::make_pair(hargs, std::make_pair(cs, cl_bs))));
                }
            }

            return clauses;
        }

        expr_ref mk_leaf(expr_ref_vector hargs, unsigned n_id) {
            expr_ref cs(m.mk_true(), m);
            mk_leaf(hargs, n_id, cs);
            return cs;
        }

        void mk_leaf(expr_ref_vector hargs, unsigned n_id, expr_ref& cs) {
            STRACE("predabst", tout << "mk_leaf: " << n_id << " ("; print_expr_ref_vector(tout, hargs, false); tout << ")\n";);
            node_info const& node = m_node2info[n_id];
            rule* r = m_rule2info[node.m_parent_rule].m_rule;
            expr_ref_vector rule_subst = get_subst_vect(r, hargs, "s");
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref conj = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
            cs = mk_conj(cs, conj);
            for (unsigned i = 0; i < usz; ++i) {
                app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                if (m_template.get_names().contains(r->get_decl(i))) { // >>> rewrite following the other model
                    cs = mk_conj(cs, expr_ref(qs_i, m));
                }
                else {
                    expr_ref_vector qs_i_vars(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                    mk_leaf(qs_i_vars, node.m_parent_nodes.get(i), cs);
                }
            }
        }

        void register_decl(model_ref const& md, func_decl* fdecl, expr* e) const {
            if (fdecl->get_arity() == 0) {
                md->register_decl(fdecl, e);
            }
            else {
                func_interp* fi = alloc(func_interp, m, fdecl->get_arity());
                fi->set_else(e);
                md->register_decl(fdecl, fi);
            }
        }

        void print_core_tree(std::ostream& out, core_tree const& core) {
            for (unsigned i = 0; i < core.size(); ++i) {
                out << "core_hname: " << core.find(i)->first << ", core_id: " << core.find(i)->second.m_node_id << ", core_ids: [";
                for (unsigned j = 0; j < core.find(i)->second.m_names.size(); ++j) {
                    out << " " << core.find(i)->second.m_names.get(j);
                }
                out << "]\n";
            }
        }

        void print_proof_prolog(std::ostream& out, unsigned id) const {
            node_set todo_nodes;
            todo_nodes.insert(id);
            while (!todo_nodes.empty()) {
                unsigned curr_id = *todo_nodes.begin();
                todo_nodes.remove(curr_id);
                node_info const& node = m_node2info[curr_id];
                out << "hyper_resolve([" << node.m_parent_nodes << "], "
                    << node.m_parent_rule << ", " << curr_id << ")." << std::endl;
                for (unsigned i = 0; i < node.m_parent_nodes.size(); ++i) {
                    todo_nodes.insert(node.m_parent_nodes[i]);
                }
            }
        }

        void print_initial_state(std::ostream& out) const {
            out << "=====================================\n";
            out << "Initial state:\n";
            out << "  Symbols:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin(),
                     end = m_func_decl2info.end(); it != end; ++it) {
                out << "    " << it->m_key->get_name() << "(";
                print_expr_ref_vector(out, it->m_value->m_vars, false);
                out << ")";
                if (it->m_value->m_is_output_predicate) {
                    out << " (output predicate)";
                }
                out << " is used by rules " << it->m_value->m_rules << std::endl;
            }
            out << "  Rules:" << std::endl;
            for (unsigned r_id = 0; r_id < m_rule2info.size(); ++r_id) {
                rule* r = m_rule2info[r_id].m_rule;
                if (r) {
                    out << "    " << r_id << ": ";
                    r->display_smt2(m, out);
                    out << std::endl;
                }
            }
            out << "  Templates:" << std::endl;
            for (unsigned i = 0; i < m_template.get_orig_templates().size(); ++i) {
                out << "    " << i << ": " << std::endl;
                rel_template const& orig = m_template.get_orig_templates().get(i);
                out << "          orig: " << orig.m_head << " <- " << orig.m_body << std::endl;
                rel_template const& temp = m_template.get_templates().get(i);
                out << "          temp: " << temp.m_head << " <- " << temp.m_body << std::endl;
            }
            out << "=====================================\n";
        }

        void print_refinement_state(std::ostream& out, unsigned refine_count) const {
            out << "=====================================\n";
            out << "State before refinement step " << refine_count << ":\n";
            out << "  Symbols:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin(),
                end = m_func_decl2info.end(); it != end; ++it) {
                out << "    " << it->m_key->get_name() << "(";
                print_expr_ref_vector(out, it->m_value->m_vars, false);
                out << ") has ";
                if (it->m_value->m_preds.size() == 0) {
                    out << "no ";
                }
                out << "predicates ";
                print_expr_ref_vector(out, it->m_value->m_preds);
            }
            out << "  Template instances:" << std::endl;
            for (unsigned i = 0; i < m_template.get_template_instances().size(); ++i) {
                out << "    " << i << ": " << std::endl;
                rel_template const& instance = m_template.get_template_instances().get(i);
                out << "          inst: " << instance.m_head << " <- " << instance.m_body << std::endl;
            }
            out << "  Instantiated rules:" << std::endl;
            for (unsigned r_id = 0; r_id < m_rule2info.size(); ++r_id) {
                out << "    " << r_id << ": "
                    << mk_pp(m_rule2info[r_id].m_body, m) << std::endl;
                out << "      head preds: ";
                print_expr_ref_vector(out, m_rule2info[r_id].m_head_preds);
                vector<expr_ref_vector> const& body_preds_vector = m_rule2info[r_id].m_body_preds;
                for (unsigned i = 0; i < body_preds_vector.size(); ++i) {
                    out << "      body preds " << i << ": ";
                    print_expr_ref_vector(out, body_preds_vector[i]);
                }
            }
            out << "=====================================\n";
        }

        void print_inference_state(std::ostream& out, unsigned refine_count, unsigned infer_count) const {
            out << "=====================================\n";
            out << "State before inference step " << refine_count << "." << infer_count << ":\n";
            out << "  Nodes:" << std::endl;
            for (unsigned i = 0; i < m_node2info.size(); ++i) {
                node_info const& node = m_node2info[i];
                out << "    " << i << ": rule " << node.m_parent_rule
                    << " applied to nodes (" << node.m_parent_nodes
                    << ") giving cube [" << node.m_cube
                    << "] for " << node.m_func_decl->get_name()
                    << std::endl;
            }
            out << "  Max reached nodes:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin(),
                end = m_func_decl2info.end(); it != end; ++it) {
                if (it->m_value->m_is_output_predicate) {
                    // Skip output predicates since they will never be reachable.
                    CASSERT("predabst", it->m_value->m_max_reach_nodes.num_elems() == 0);
                }
                else {
                    out << "    " << it->m_key->get_name() << ": "
                        << it->m_value->m_max_reach_nodes << std::endl;
                }
            }
            out << "  Worklist: " << m_node_worklist << std::endl;
            out << "=====================================\n";
        }

        void print_expr_ref_vector(std::ostream& out, expr_ref_vector const& v,
                                   bool newline = true) const {
            for (unsigned i = 0; i < v.size(); ++i) {
                out << mk_pp(v[i], m);
                if (i + 1 < v.size()) {
                    out << ", ";
                }
            }
            if (newline) {
                out << std::endl;
            }
        }
    };

    predabst::predabst(context& ctx):
        engine_base(ctx.get_manager(), "predabst"),
        m_imp(alloc(imp, ctx)) {
    }
    predabst::~predabst() {
        dealloc(m_imp);
    }
    lbool predabst::query(expr* query) {
        return m_imp->query(query);
    }
    void predabst::cancel() {
        m_imp->cancel();
    }
    void predabst::cleanup() {
        m_imp->cleanup();
    }
    void predabst::reset_statistics() {
        m_imp->reset_statistics();
    }
    void predabst::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void predabst::display_certificate(std::ostream& out) const {
        m_imp->display_certificate(out);
    }
    expr_ref predabst::get_answer() {
        return m_imp->get_answer();
    }
    model_ref predabst::get_model() {
        return m_imp->get_model();
    }
};

template<class T>
inline std::ostream& operator<<(std::ostream& out, vector<T> const& v) {
    unsigned size = v.size();
    if (size > 0) {
        out << v[0];
        for (unsigned i = 1; i < size; ++i) out << "," << v[i];
    }
    return out;
}
