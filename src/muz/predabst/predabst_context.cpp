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
#include "simplifier.h"
#include "arith_simplifier_plugin.h"
#include "substitution.h"
#include "smt_kernel.h"
#include "dl_transforms.h"
#include "fixedpoint_params.hpp"
#include <vector>
#include <algorithm>

#define PREDABST_COMPLETE_CUBE
#define PREDABST_ORDER_CARTPROD_CHOICES
#undef PREDABST_ASSERT_EXPR_UPFRONT
#define PREDABST_PRE_SIMPLIFY
#define PREDABST_NO_SIMPLIFY

namespace datalog {

    struct core_tree_node {
        unsigned         m_node_id;
        vector<unsigned> m_names;
        core_tree_node(unsigned node_id) :
            m_node_id(node_id) {}
    };

    struct core_clause {
        unsigned        m_name;
        expr_ref_vector m_args;
        expr_ref        m_body;
        core_clause(unsigned name, expr_ref_vector const& args, expr_ref const& body) :
            m_name(name),
            m_args(args),
            m_body(body) {}
    };

    typedef vector<core_tree_node> core_tree;
    typedef vector<core_clause> core_clauses; // just a sequence; the index has no meaning

    struct refine_cand_info {
    private:
        static vector<expr_ref_vector>               m_empty;

    public:
        obj_map<func_decl, vector<expr_ref_vector> > m_allrels_info;

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

    vector<expr_ref_vector> refine_cand_info::m_empty;

    struct refine_pred_info {
        expr_ref        m_pred;
        expr_ref_vector m_pred_vars;
        refine_pred_info(expr_ref const& pred, expr_ref_vector const& pred_vars) :
            m_pred(pred),
            m_pred_vars(pred_vars) {}
    };

    class predabst::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            /*
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsumed;
            */
            unsigned m_num_refinement_iterations;
            unsigned m_num_predabst_iterations;
            unsigned m_num_solver_assert_invocations;
            unsigned m_num_solver_check_interp_invocations;
            unsigned m_num_solver_check_body_invocations;
            unsigned m_num_solver_check_head_invocations;
            unsigned m_num_rules_unsatisfiable;
            unsigned m_num_rules_succeeded;
            unsigned m_num_rules_failed;
            unsigned m_num_nodes_created;
            unsigned m_num_nodes_suppressed;
            unsigned m_num_nodes_subsumed;
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

        struct pred_info {
            expr_ref         m_pred;
            bool             m_root_pred;
#ifndef PREDABST_COMPLETE_CUBE
            vector<unsigned> m_implied;
#endif
            pred_info(expr_ref const& pred) :
                m_pred(pred),
                m_root_pred(false) {}
            pred_info(app_ref const& pred) :
                m_pred(expr_ref(pred.get(), pred.m())),
                m_root_pred(false) {}
        };

        struct func_decl_info {
            expr_ref_vector   m_vars;
            vector<pred_info> m_preds;
#ifndef PREDABST_COMPLETE_CUBE
            vector<unsigned>  m_root_preds;
#endif
            uint_set          m_users;
            node_set          m_max_reach_nodes;
            bool              m_is_output_predicate;
            bool              m_is_wf_predicate;
            bool              m_has_template;
            func_decl_info(expr_ref_vector const& vars, bool is_output_predicate, bool is_wf_predicate) :
                m_vars(vars),
                m_is_output_predicate(is_output_predicate),
                m_is_wf_predicate(is_wf_predicate),
                m_has_template(false) {}
        };

#ifdef PREDABST_ASSERT_EXPR_UPFRONT
        struct rule_instance_info {
            expr_ref_vector         m_head_pred_cond_vars;
            vector<expr_ref_vector> m_body_pred_cond_vars;
            smt::kernel*            m_rule_solver;
            rule_instance_info(ast_manager& m) :
                m_head_pred_cond_vars(m),
                m_rule_solver(NULL) {}
            unsigned uninterpreted_tail_size() const {
                return m_body_pred_cond_vars.size();
            }
            void reset() {
                m_head_pred_cond_vars.reset();
                m_body_pred_cond_vars.reset();
                m_rule_solver->reset();
            }
            void cancel() {
                m_rule_solver->cancel();
            }
            void reset_cancel() {
                m_rule_solver->reset_cancel();
            }
            void alloc_solver(ast_manager& m, smt_params& fparams) {
                CASSERT("predabst", !m_rule_solver);
                m_rule_solver = alloc(smt::kernel, m, fparams);
            }
            void dealloc_solver() {
                CASSERT("predabst", m_rule_solver);
                dealloc(m_rule_solver);
                m_rule_solver = NULL;
            }
            void display(std::ostream& out) const {
                out << "      head preds cond vars: ";
                print_expr_ref_vector(out, m_head_pred_cond_vars);
                for (unsigned i = 0; i < m_body_pred_cond_vars.size(); ++i) {
                    out << "      body pred cond vars " << i << ": ";
                    print_expr_ref_vector(out, m_body_pred_cond_vars[i]);
                }
            }
        };
#else
        struct rule_instance_info {
            expr_ref_vector         m_body;
            expr_ref_vector         m_head_preds;
            vector<expr_ref_vector> m_body_preds;
            bool                    m_unsat;
            rule_instance_info(ast_manager& m) :
                m_body(m),
                m_head_preds(m) {}
            unsigned uninterpreted_tail_size() const {
                return m_body_preds.size();
            }
            void reset() {
                m_body.reset();
                m_head_preds.reset();
                m_body_preds.reset();
            }
            void cancel() {}
            void reset_cancel() {}
            void alloc_solver(ast_manager& m, smt_params& fparams) {}
            void dealloc_solver() {}
            void display(std::ostream& out) const {
                out << "      body: ";
                print_expr_ref_vector(out, m_body);
                out << "      head preds: ";
                print_expr_ref_vector(out, m_head_preds);
                for (unsigned i = 0; i < m_body_preds.size(); ++i) {
                    out << "      body preds " << i << ": ";
                    print_expr_ref_vector(out, m_body_preds[i]);
                }
            }
        };
#endif

        struct rule_info {
            func_decl*              m_func_decl;
            rule*                   m_rule;
            unsigned                m_template_id;
            rule_instance_info      m_instance_info;
            bool                    m_unsat;
            rule_info(func_decl* func_decl, rule* rule, unsigned template_id, ast_manager& m) :
                m_func_decl(func_decl),
                m_rule(rule),
                m_template_id(template_id),
                m_instance_info(m) {}
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

        static const unsigned NON_NODE = UINT_MAX;

        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        fixedpoint_params const& m_fp_params;
        smt_params             m_fparams;     // parameters specific to smt solving
#ifndef PREDABST_ASSERT_EXPR_UPFRONT
        smt::kernel            m_solver;      // basic SMT solver class
#endif
        mutable var_subst      m_var_subst;   // substitution object. It gets updated and reset.
#ifdef PREDABST_PRE_SIMPLIFY
        simplifier             m_simplifier;
#endif
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
            acr_error() {}
            acr_error(unsigned node, acr_error_kind kind) :
                m_node(node),
                m_kind(kind) {}
        };

        struct core_tree_info {
            unsigned            m_root_name;
            expr_ref_vector     m_root_args;
            unsigned            m_last_name;
            unsigned            m_last_pos;
            core_tree           m_core;
            core_tree_info(ast_manager& m) :
                m_root_args(m) {}
            core_tree_info(unsigned root_name, expr_ref_vector const& root_args, unsigned last_name, unsigned last_pos, core_tree const& core) :
                m_root_name(root_name),
                m_root_args(root_args),
                m_last_name(last_name),
                m_last_pos(last_pos),
                m_core(core) {}
        };

        struct core_tree_wf_info {
            expr_ref         m_bound;
            expr_ref         m_decrease;
            refine_cand_info m_refine_info;
            core_tree_wf_info(ast_manager& m) :
                m_bound(m),
                m_decrease(m) {}
        };

    public:
        imp(ast_manager& m, fixedpoint_params const& fp_params) :
            m(m),
            m_fp_params(fp_params),
#ifndef PREDABST_ASSERT_EXPR_UPFRONT
            m_solver(m, m_fparams),
#endif
            m_var_subst(m, false),
#ifdef PREDABST_PRE_SIMPLIFY
            m_simplifier(m),
#endif
            m_cancel(false),
            m_func_decls(m),
            m_template(m) {

            m_fparams.m_mbqi = false;
            m_fparams.m_model = false;
#ifdef PREDABST_NO_SIMPLIFY
            m_fparams.m_preprocess = false;
#endif

#ifdef PREDABST_PRE_SIMPLIFY
            basic_simplifier_plugin* bsimp = alloc(basic_simplifier_plugin, m);
            m_simplifier.register_plugin(bsimp);
            m_simplifier.register_plugin(alloc(arith_simplifier_plugin, m, *bsimp, m_fparams));
#endif
        }

        ~imp() {
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin(),
                end = m_func_decl2info.end(); it != end; ++it) {
                dealloc(it->m_value);
            }
            for (unsigned i = 0; i < m_rule2info.size(); ++i) {
                m_rule2info[i].m_instance_info.dealloc_solver();
            }
        }

        lbool query(rule_set& rules) {
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

            CASSERT("predabst", m_rule2info.empty());
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                m_rule2info.push_back(rule_info(r->get_decl(), r, 0, m));
            }
            for (unsigned i = 0; i < m_template.get_num_templates(); ++i) {
                m_rule2info.push_back(rule_info(m_template.get_template(i).m_head->get_decl(), nullptr, i, m));
            }

            for (unsigned i = 0; i < m_rule2info.size(); ++i) {
                m_rule2info[i].m_instance_info.alloc_solver(m, m_fparams);
            }

            return abstract_check_refine();
        }

        void cancel() {
            m_cancel = true;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < m_rule2info.size(); ++i) {
                m_rule2info[i].m_instance_info.cancel();
            }
#else
            m_solver.cancel();
#endif
        }

        void cleanup() {
            m_cancel = false;
            // TBD hmm?
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < m_rule2info.size(); ++i) {
                m_rule2info[i].m_instance_info.reset_cancel();
            }
#else
            m_solver.reset_cancel();
#endif
        }

        void reset_statistics() {
            m_stats.reset();
        }

        void collect_statistics(statistics& st) const {
#define UPDATE_STAT(NAME) st.update(#NAME, m_stats.NAME)
            UPDATE_STAT(m_num_refinement_iterations);
            UPDATE_STAT(m_num_predabst_iterations);
            UPDATE_STAT(m_num_solver_assert_invocations);
            UPDATE_STAT(m_num_solver_check_interp_invocations);
            UPDATE_STAT(m_num_solver_check_head_invocations);
            UPDATE_STAT(m_num_solver_check_body_invocations);
            UPDATE_STAT(m_num_rules_unsatisfiable);
            UPDATE_STAT(m_num_rules_succeeded);
            UPDATE_STAT(m_num_rules_failed);
            UPDATE_STAT(m_num_nodes_created);
            UPDATE_STAT(m_num_nodes_suppressed);
            UPDATE_STAT(m_num_nodes_subsumed);
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
                    vector<pred_info> const& preds = m_func_decl2info[fdecl]->m_preds;
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

        // Returns true if v1 is a (possibly non-strict) subset of v2.
        static bool is_subset(expr_ref_vector const& v1, expr_ref_vector const& v2) {
            for (unsigned i = 0; i < v1.size(); ++i) {
                if (!v2.contains(v1.get(i))) {
                    return false;
                }
            }
            return true;
        }

        // Apply a substitution vector to an expression, returning the result.
        expr_ref apply_subst(expr* expr, expr_ref_vector const& subst) const {
            expr_ref expr2(m);
            m_var_subst(expr, subst.size(), subst.c_ptr(), expr2);
            return expr2;
        }

        // Apply a substitution vector to an application expression, returning the result.
        app_ref apply_subst(app* app, expr_ref_vector const& subst) const {
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

        // Apply a substitution vector to each expression in a vector of
        // expressions, returning the result.
        expr_ref_vector apply_subst(vector<pred_info> const& preds, expr_ref_vector const& subst) {
            expr_ref_vector exprs2(m);
            exprs2.reserve(preds.size());
            for (unsigned i = 0; i < preds.size(); ++i) {
                exprs2[i] = apply_subst(preds[i].m_pred, subst);
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
                arg_vars[i] = m.mk_var(i, fdecl->get_domain(i));
            }
            return arg_vars;
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) covering all the variables used by r, which maps the variables
        // used as head arguments to hvars, and maps all variables that do not
        // appear in the head to fresh contants.
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

        static bool args_are_distinct_vars(app* a) {
            vector<bool> used;
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                if (!is_var(a->get_arg(i))) {
                    return false;
                }
                unsigned idx = to_var(a->get_arg(i))->get_idx();
                if (idx >= used.size()) {
                    used.resize(idx + 1);
                }
                if (used.get(idx)) {
                    return false;
                }
                used[idx] = true;
            }
            return true;
        }

        // Returns true if e contains any variables other than those in bound.
        static bool has_free_vars(expr* e, expr_ref_vector const& bound) {
            if (is_var(e)) {
                return !bound.contains(e);
            }
            if (is_app(e)) {
                app* a = to_app(e);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    if (has_free_vars(a->get_arg(i), bound)) {
                        return true;
                    }
                }
            }
            return false;
        }

        // Returns true if e contains any variables.
        bool has_vars(expr* e) const {
            return has_free_vars(e, expr_ref_vector(m));
        }

#ifndef PREDABST_COMPLETE_CUBE
        void add_implied_to_cube(cube_t& cube, vector<pred_info> const& preds, unsigned idx) {
            CASSERT("predabst", !cube[idx]);
            cube[idx] = true;
            for (unsigned i = 0; i < preds[idx].m_implied.size(); ++i) {
                add_implied_to_cube(cube, preds, preds[idx].m_implied[i]);
            }
        }

        // Return the completion of cube, i.e. the vector containing all predicates that are implied by those in cube.
        cube_t complete_cube(cube_t const& cube, func_decl* fdecl) {
            cube_t completion;
            for (unsigned i = 0; i < cube.size(); ++i) {
                if (cube[i]) {
                    add_implied_to_cube(completion, m_func_decl2info[fdecl]->m_preds, i);
                }
            }
            return completion;
        }
#endif

        // Returns whether c1 implies c2, or in other words, whether the set
        // represented by c1 is a (non-strict) subset of that represented by c2.
        static bool complete_cube_leq(cube_t const& c1, cube_t const& c2) {
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

        bool cube_leq(cube_t const& c1, cube_t const& c2, func_decl* fdecl) {
#ifdef PREDABST_COMPLETE_CUBE
            return complete_cube_leq(c1, c2);
#else
            return complete_cube_leq(complete_cube(c1, fdecl), c2);
#endif
        }

        expr_ref cube_to_formula(cube_t const& cube, vector<pred_info> const& preds) const {
            expr_ref_vector es(m);
            for (unsigned i = 0; i < cube.size(); ++i) {
                if (cube[i]) {
                    es.push_back(preds[i].m_pred);
                }
            }
            return mk_conj(es);
        }

        static bool is_regular_predicate(func_decl const* fdecl) {
            return !is_predicate_list(fdecl) && !is_template_extra(fdecl) && !is_template(fdecl);
        }

        void find_all_func_decls(rule_set const& rules) {
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                if (is_regular_predicate(r->get_decl())) {
                    for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                        func_decl* fdecl = r->get_decl(j);
                        if (is_predicate_list(fdecl)) {
                            STRACE("predabst", tout << "Error: found predicate list " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found predicate list " + fdecl->get_name().str() + " in non-head position");
                        }
                        if (is_template_extra(fdecl)) {
                            STRACE("predabst", tout << "Error: found extra template constraint in non-head position\n";);
                            throw default_exception("found extra template constraint in non-head position");
                        }
                        if (is_template(fdecl)) {
                            STRACE("predabst", tout << "Error: found template " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found template " + fdecl->get_name().str() + " in non-head position");
                        }
                        process_func_decl(rules, fdecl);
                    }
                    process_func_decl(rules, r->get_decl());
                }
            }
        }

        void process_func_decl(rule_set const& rules, func_decl *fdecl) {
            CASSERT("predabst", is_regular_predicate(fdecl));
            CASSERT("predabst", fdecl->get_range() == m.mk_bool_sort());
            if (!m_func_decl2info.contains(fdecl)) {
                bool is_wf = is_wf_predicate(fdecl);
                if (is_wf) {
                    if (fdecl->get_arity() % 2 != 0) {
                        STRACE("predabst", tout << "Error: WF predicate symbol " << fdecl->get_name() << " has arity " << fdecl->get_arity() << " which is odd\n";);
                        throw default_exception("WF predicate symbol " + fdecl->get_name().str() + " has odd arity");
                    }
                    for (unsigned i = 0; i < fdecl->get_arity() / 2; ++i) {
                        unsigned j = fdecl->get_arity() / 2 + i;
                        if (fdecl->get_domain(i) != fdecl->get_domain(j)) {
                            STRACE("predabst", tout << "Error: WF predicate symbol " << fdecl->get_name() << " has argument " << i << " of type " << mk_pp(fdecl->get_domain(i), m) << " and argument " << j << " of type " << mk_pp(fdecl->get_domain(j), m) << "\n";);
                            throw default_exception("WF predicate symbol " + fdecl->get_name().str() + " has mismatching argument types");
                        }
                        // The following restriction may be removed in future.
                        if (fdecl->get_domain(i) != arith_util(m).mk_int()) {
                            STRACE("predabst", tout << "Error: WF predicate symbol " << fdecl->get_name() << " has argument " << i << " of type " << mk_pp(fdecl->get_domain(i), m) << " which is not int\n";);
                            throw default_exception("WF predicate symbol " + fdecl->get_name().str() + " has non-integer argument types");
                        }
                    }
                }

                m_func_decls.push_back(fdecl);
                expr_ref_vector vars = get_arg_vars(fdecl);
                m_func_decl2info.insert(fdecl, alloc(func_decl_info, vars, rules.is_output_predicate(fdecl), is_wf));
            }
        }

        bool is_wf_predicate(func_decl const* pred) const {
            return pred->get_name().str().substr(0, 6) == "__wf__";
        }

        void process_special_rules(rule_set& rules, bool(*p)(func_decl const*), void (imp::*f)(rule const*)) {
            ptr_vector<rule> to_delete;
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                if (p(r->get_decl())) {
                    (this->*f)(r);
                    to_delete.push_back(r);
                }
            }

            for (unsigned i = 0; i < to_delete.size(); ++i) {
                rules.del_rule(to_delete[i]);
            }
        }

        static bool is_predicate_list(func_decl const* fdecl) {
            return fdecl->get_name().str().substr(0, 8) == "__pred__";
        }

        void collect_predicate_list(rule const* r) {
            CASSERT("predabst", is_predicate_list(r->get_decl()));
            // r is a rule of the form:
            //   p1 AND ... AND pN => __pred__SUFFIX
            // Treat p1...pN as initial predicates for query symbol SUFFIX.
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            STRACE("predabst", tout << "Found predicate list for query symbol " << suffix << "("; print_expr_ref_vector(tout, expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()), false); tout << ")\n";);

            func_decl_ref suffix_decl(m.mk_func_decl(
                suffix,
                head_decl->get_arity(),
                head_decl->get_domain(),
                head_decl->get_range()), m);
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found predicate list for non-existent query symbol\n";);
                throw default_exception("found predicate list for non-existent query symbol " + suffix.str());
            }

            if (!args_are_distinct_vars(r->get_head())) {
                STRACE("predabst", tout << "Error: predicate list has invalid argument list\n";);
                throw default_exception("predicate list for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: predicate list has an uninterpreted tail\n";);
                throw default_exception("predicate list for " + suffix.str() + " has an uninterpreted tail");
            }

            // Add p1..pN to m_func_decl2info[SUFFIX].m_preds.
            expr_ref_vector const& vars = m_func_decl2info[suffix_decl]->m_vars;
            vector<pred_info>& preds = m_func_decl2info[suffix_decl]->m_preds;
            expr_ref_vector subst = build_subst(r->get_head()->get_args(), vars);
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                if (has_free_vars(r->get_tail(i), expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()))) {
                    STRACE("predabst", tout << "Error: predicate has free variables\n";);
                    throw default_exception("predicate for " + suffix.str() + " has free variables");
                }

                app_ref pred = apply_subst(r->get_tail(i), subst);
                STRACE("predabst", tout << "  predicate " << i << ": " << mk_pp(pred, m) << "\n";);
                preds.push_back(pred_info(pred));
            }
        }

        static bool is_template_extra(func_decl const* fdecl) {
            return fdecl->get_name() == "__temp__extra__";
        }

        void collect_template_extra(rule const* r) {
            CASSERT("predabst", is_template_extra(r->get_decl()));
            // r is a rule of the form:
            //  ??? => __temp__extra__
            // Treat ??? as an extra template constraint.
            func_decl* head_decl = r->get_decl();
            STRACE("predabst", tout << "Found extra template constraint with " << head_decl->get_arity() << " parameters\n";);
            CASSERT("predabst", r->get_decl()->get_range() == m.mk_bool_sort());

            if (m_template.get_params().size() > 0) {
                STRACE("predabst", tout << "Error: found multiple extra template constraints\n";);
                throw default_exception("found multiple extra template constraints");
            }

            if (!args_are_distinct_vars(r->get_head())) {
                STRACE("predabst", tout << "Error: extra template constraint has invalid argument list\n";);
                throw default_exception("extra template constraint has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: extra template constraint has an uninterpreted tail\n";);
                throw default_exception("extra template constraint has an uninterpreted tail");
            }

            // Replace the variables corresponding to the extra template parameters with fresh constants.
            expr_ref_vector extra_params = get_fresh_args(r->get_decl(), "b");
            expr_ref_vector extra_subst = build_subst(r->get_head()->get_args(), extra_params);
            expr_ref extras = apply_subst(mk_conj(expr_ref_vector(m, r->get_tail_size(), r->get_expr_tail())), extra_subst);
            STRACE("predabst", tout << "  " << mk_pp(extras, m) << "\n";);

            if (has_vars(extras)) {
                STRACE("predabst", tout << "Error: extra template constraint has free variables\n";);
                throw default_exception("extra template constraint has free variables");
            }

            m_template.process_template_extra(extra_params, extras);
        }

        static bool is_template(func_decl const* fdecl) {
            return (fdecl->get_name().str().substr(0, 8) == "__temp__") && !is_template_extra(fdecl);
        }

        void collect_template(rule const* r) {
            CASSERT("predabst", is_template(r->get_decl()));
            // r is a rule of the form:
            //  ??? => __temp__SUFFIX
            // Treat ??? as a template for query symbol SUFFIX.
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            STRACE("predabst", tout << "Found template for query symbol " << suffix << "\n";);

            expr_ref_vector const& extra_params = m_template.get_params();
            unsigned num_extras = extra_params.size();
            if (head_decl->get_arity() < num_extras) {
                STRACE("predabst", tout << "Error: template has insufficient parameters for the extra template parameters\n";);
                throw default_exception("template for " + suffix.str() + " has insufficient parameters");
            }

            unsigned new_arity = head_decl->get_arity() - num_extras;
            for (unsigned i = 0; i < num_extras; ++i) {
                if (head_decl->get_domain(new_arity + i) != to_app(extra_params[i])->get_decl()->get_range()) {
                    STRACE("predabst", tout << "Error: extra template parameter " << i << " is of wrong type\n";);
                    throw default_exception("extra parameter to template for " + suffix.str() + " is of wrong type");
                }
            }

            func_decl_ref suffix_decl(m.mk_func_decl(
                suffix,
                new_arity,
                head_decl->get_domain(),
                head_decl->get_range()), m);
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found template for non-existent query symbol\n";);
                throw default_exception("found template for non-existent query symbol " + suffix.str());
            }

            if (m_func_decl2info[suffix_decl]->m_has_template) {
                STRACE("predabst", tout << "Error: found multiple templates for " << suffix.str() << "\n";);
                throw default_exception("found multiple templates for " + suffix.str());
            }

            m_func_decl2info[suffix_decl]->m_has_template = true;

            if (!args_are_distinct_vars(r->get_head())) {
                STRACE("predabst", tout << "Error: template for has invalid argument list\n";);
                throw default_exception("template for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: template has an uninterpreted tail\n";);
                throw default_exception("template for " + suffix.str() + " has an uninterpreted tail");
            }

            // Replace the variables corresponding to the extra template parameters with their corresponding constants.
            app_ref head(m.mk_app(suffix_decl, r->get_head()->get_args()), m);
            expr_ref_vector extra_subst = build_subst(r->get_head()->get_args() + new_arity, extra_params);
            expr_ref body = apply_subst(mk_conj(expr_ref_vector(m, r->get_tail_size(), r->get_expr_tail())), extra_subst);
            STRACE("predabst", tout << "  " << mk_pp(head, m) << " := " << mk_pp(body, m) << "\n";);

            if (has_free_vars(body, expr_ref_vector(m, new_arity, r->get_head()->get_args()))) {
                STRACE("predabst", tout << "Error: template has free variables\n";);
                throw default_exception("template for " + suffix.str() + " has free variables");
            }

            // Generate fresh constants for each of the query parameters.
            expr_ref_vector query_params = get_fresh_args(r->get_decl(), "v", new_arity);
            app_ref temp_inst_head(m.mk_app(suffix_decl, query_params.c_ptr()), m);

            m_template.process_template(rel_template(head, body), temp_inst_head);
        }

        void find_rule_uses(rule_set const& rules) {
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                CASSERT("predabst", is_regular_predicate(r->get_decl()));

                if (m_func_decl2info[r->get_decl()]->m_has_template) {
                    STRACE("predabst", tout << "Rule exists for " << r->get_decl()->get_name() << ", which also has a template\n";);
                    throw default_exception("both rule and template for " + r->get_decl()->get_name().str());
                }

                for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                    m_func_decl2info[r->get_decl(j)]->m_users.insert(i);
                }
            }
        }

#define RETURN_CHECK_CANCELLED(result) return m_cancel ? l_undef : result;

        lbool abstract_check_refine() {
            STRACE("predabst", print_initial_state(tout););

            if (!m_template.instantiate_templates()) {
                STRACE("predabst", tout << "Initial template refinement unsuccessful: result is UNSAT\n";);
                RETURN_CHECK_CANCELLED(l_true);
            }

            // The only things that change on subsequent iterations of this loop are
            // the predicate lists
            // (m_func_decl2info::m_preds) and m_template.  The latter can have an
            // effect on the execution of the algorithm via the initial nodes
            // set up by initialize_abs.
            unsigned refine_count = 0;
            while (true) {
                m_stats.m_num_refinement_iterations++;
                m_node2info.reset();
                for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                    func_decl* fdecl = m_func_decls.get(i);
                    m_func_decl2info[fdecl]->m_max_reach_nodes.reset();

#ifndef PREDABST_COMPLETE_CUBE
                    // Set up m_func_decl2info::m_preds::m_implied for this iteration.
                    expr_ref_vector const& vars = m_func_decl2info[fdecl]->m_vars;
                    vector<pred_info>& preds = m_func_decl2info[fdecl]->m_preds;
                    for (unsigned j = 0; j < preds.size(); ++j) {
                        preds[j].m_implied.reset();
                        preds[j].m_root_pred = true;
                    }

                    expr_ref_vector subst = build_subst(vars, get_fresh_args(fdecl, "a"));
                    expr_ref_vector inst_preds = apply_subst(preds, subst);
                     
                    for (unsigned j = 0; j < preds.size(); ++j) {
                        for (unsigned k = 0; k < preds.size(); ++k) {
                            if (j != k) {
                                // Does preds[j] imply preds[k]?
                                smt_params new_param;
                                smt::kernel solver(m, new_param);
                                solver.assert_expr(inst_preds.get(j));
                                solver.assert_expr(expr_ref(m.mk_not(inst_preds.get(k)), m));
                                if (!solver.check()) {
                                    // preds[j] implies preds[k].
                                    preds[j].m_implied.push_back(k);
                                    preds[k].m_root_pred = false;
                                }
                            }
                        }
                    }

                    m_func_decl2info[fdecl]->m_root_preds.reset();
                    for (unsigned j = 0; j < preds.size(); ++j) {
                        if (preds[j].m_root_pred) {
                            m_func_decl2info[fdecl]->m_root_preds.push_back(j);
                        }
                    }

                    STRACE("predabst", print_preds_forest(tout, fdecl););

                    // Debug code: check that every predicate appears precisely once in the forest.
                    cube_t full_cube;
                    full_cube.resize(m_func_decl2info[fdecl]->m_preds.size());
                    for (unsigned j = 0; j < m_func_decl2info[fdecl]->m_root_preds.size(); ++j) {
                        add_implied_to_cube(full_cube, m_func_decl2info[fdecl]->m_preds, m_func_decl2info[fdecl]->m_root_preds[j]);
                    }
                    for (unsigned j = 0; j < full_cube.size(); ++j) {
                        CASSERT("predabst", full_cube[j]);
                    }
#endif
                }

                // Set up m_rule2info for this iteration:
                // for each rule: ground body and instantiate predicates for applications
                for (unsigned r_id = 0; !m_cancel && r_id < m_rule2info.size(); ++r_id) {
                    instantiate_rule(r_id);
                }

                STRACE("predabst", print_refinement_state(tout, refine_count););

                acr_error error;
                if (find_solution(refine_count, error)) {
                    STRACE("predabst", tout << "Solution found: result is SAT\n";);
                    RETURN_CHECK_CANCELLED(l_false);
                }
                else if (!m_fp_params.use_refinement()) {
                    STRACE("predabst", tout << "No solution found: result is UNSAT\n";);
                    RETURN_CHECK_CANCELLED(l_true);
                }
                else {
                    // Our attempt to find a solution failed and we want to try refinement.
                    core_tree_info core_info(m);
                    core_tree_wf_info core_info_wf(m);
                    if (mk_core_tree(error.m_node, core_info)) {
                        // The result didn't hold up without abstraction.  We
                        // need to refine the predicates and retry.
                        if (!refine_predicates(core_info)) {
                            STRACE("predabst", tout << "Predicate refinement unsuccessful: result is UNKNOWN\n";);
                            RETURN_CHECK_CANCELLED(l_undef);
                        }

                        STRACE("predabst", tout << "Predicate refinement successful: retrying\n";);
                    }
                    else if ((error.m_kind == not_wf) && should_refine_predicates_not_wf(error.m_node, core_info_wf)) {
                        // The result relating to WF didn't hold up without abstraction.  We
                        // need to refine the predicates and retry.
                        if (!refine_predicates_not_wf(core_info_wf)) {
                            STRACE("predabst", tout << "WF predicate refinement unsuccessful: result is UNKNOWN\n";);
                            RETURN_CHECK_CANCELLED(l_undef);
                        }
 
                        STRACE("predabst", tout << "WF predicate refinement successful: retrying\n";);
                    }
                    else {
                        // The result held up even without abstraction.  Unless
                        // we can refine the templates, we have a proof of
                        // unsatisfiability.
                        if (m_template.get_num_templates() == 0) {
                            STRACE("predabst", tout << "No templates to refine: result is UNSAT\n";);
                            RETURN_CHECK_CANCELLED(l_true);
                        }
                        else if (!refine_templates(error)) {
                            STRACE("predabst", tout << "Template refinement unsuccessful: result is UNSAT\n";);
                            RETURN_CHECK_CANCELLED(l_true);
                        }

                        STRACE("predabst", tout << "Template refinement successful: retrying\n";);
                    }
                }

                refine_count++;
            }
        }

        void instantiate_rule(unsigned r_id) {
            rule* r = m_rule2info[r_id].m_rule;
            if (r) {
                instantiate_regular_rule(r, r_id);
            }
            else {
                instantiate_template_rule(m_rule2info[r_id].m_template_id, r_id);
            }

            m_rule2info[r_id].m_unsat = !rule_body_satisfiable(r_id);
        }

        void invert(expr_ref_vector& exprs) {
            for (unsigned i = 0; i < exprs.size(); ++i) {
                exprs[i] = m.mk_not(exprs.get(i));
            }
        }

        void pre_simplify(expr_ref_vector& exprs) {
#ifdef PREDABST_PRE_SIMPLIFY
            for (unsigned i = 0; i < exprs.size(); ++i) {
                proof_ref pr(m);
                expr_ref e(exprs.get(i), m);
                m_simplifier(e, e, pr);
                exprs[i] = e;
            }
#endif
        }

        void instantiate_regular_rule(rule* r, unsigned r_id) {
            STRACE("predabst", tout << "Instantiating rule " << r_id << "\n";);
            rule_instance_info& info = m_rule2info[r_id].m_instance_info;
            info.reset();

            // create grounding substitution
            expr_ref_vector rule_subst = get_subst_vect_free(r, "c");

            // create ground body
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref_vector body = apply_subst(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz), rule_subst);
            STRACE("predabst", tout << "  body: "; print_expr_ref_vector(tout, body););
            pre_simplify(body);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                info.m_rule_solver->assert_expr(body.get(i));
            }
#else
            info.m_body.swap(body);
#endif

            // create instantiations for non-query head
            if (!m_func_decl2info[r->get_decl()]->m_is_output_predicate) {
                expr_ref_vector heads = app_inst_preds(apply_subst(r->get_head(), rule_subst));
                STRACE("predabst", tout << "  head preds: "; print_expr_ref_vector(tout, heads););
                invert(heads);
                pre_simplify(heads);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                expr_ref_vector head_cond_vars = assert_exprs_upfront(heads, info.m_rule_solver);
                info.m_head_pred_cond_vars.swap(head_cond_vars);
#else
                info.m_head_preds.swap(heads);
#endif
            }

            // create instantiations for body applications
            for (unsigned i = 0; i < usz; ++i) {
                expr_ref_vector tails = app_inst_preds(apply_subst(r->get_tail(i), rule_subst));
                STRACE("predabst", tout << "  body preds " << i << ": "; print_expr_ref_vector(tout, tails););
                pre_simplify(tails);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                expr_ref_vector tail_cond_vars = assert_exprs_upfront(tails, info.m_rule_solver);
                info.m_body_pred_cond_vars.push_back(tail_cond_vars);
#else
                info.m_body_preds.push_back(tails);
#endif
            }
        }

        void instantiate_template_rule(unsigned t_id, unsigned r_id) {
            STRACE("predabst", tout << "Instantiating template " << t_id << " (rule " << r_id << ")\n";);
            rel_template const& instance = m_template.get_template_instance(t_id);
            rule_instance_info& info = m_rule2info[r_id].m_instance_info;
            info.reset();

            expr_ref_vector body = get_conj_terms(instance.m_body);
            pre_simplify(body);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                info.m_rule_solver->assert_expr(body.get(i));
            }
#else
            info.m_body.swap(body);
#endif

            CASSERT("predabst", !m_func_decl2info[instance.m_head->get_decl()]->m_is_output_predicate);
            expr_ref_vector heads = app_inst_preds(instance.m_head);
            STRACE("predabst", tout << "  head preds: "; print_expr_ref_vector(tout, heads););
            invert(heads);
            pre_simplify(heads);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            expr_ref_vector head_cond_vars = assert_exprs_upfront(heads, info.m_rule_solver);
            info.m_head_pred_cond_vars.swap(head_cond_vars);
#else
            info.m_head_preds.swap(heads);
#endif
        }

        // instantiate each predicate by replacing its free variables with (grounded) arguments of gappl
        expr_ref_vector app_inst_preds(app* gappl) {
            expr_ref_vector const& vars = m_func_decl2info[gappl->get_decl()]->m_vars;
            vector<pred_info> const& preds = m_func_decl2info[gappl->get_decl()]->m_preds;
            // instantiation maps preds variables to head arguments
            expr_ref_vector inst = build_subst(vars, gappl->get_args());
            // preds instantiates to inst_preds
            return apply_subst(preds, inst);
        }

#ifdef PREDABST_ASSERT_EXPR_UPFRONT
        expr_ref_vector assert_exprs_upfront(expr_ref_vector const& preds, smt::kernel* solver) {
            expr_ref_vector cond_vars(m);
            for (unsigned i = 0; i < preds.size(); ++i) {
                expr_ref c(m.mk_fresh_const("cv", m.mk_bool_sort()), m);
                cond_vars.push_back(c);
                expr_ref e(m.mk_iff(preds.get(i), c), m);
                m_stats.m_num_solver_assert_invocations++;
                solver->assert_expr(e);
            }
            return cond_vars;
        }
#endif

        bool rule_body_satisfiable(unsigned r_id) {
            rule_instance_info const& info = m_rule2info[r_id].m_instance_info;

#ifndef PREDABST_ASSERT_EXPR_UPFRONT
            scoped_push _push1(m_solver);
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                m_solver.assert_expr(info.m_body[i]);
            }
#endif

            m_stats.m_num_solver_check_interp_invocations++;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            lbool result = info.m_rule_solver->check();
#else
            lbool result = m_solver.check();
#endif
            if (result == l_false) {
                // unsat body
                STRACE("predabst", tout << "Rule " << r_id << " will always fail\n";);
                m_stats.m_num_rules_unsatisfiable++;
                return false;
            }
            else {
                return true;
            }
        }

		expr_ref model_eval_app(model_ref const& md, app const* app) {
			expr_ref exp(m);
			bool result = md->eval(app->get_decl(), exp);
            CASSERT("predabst", result);
            ptr_vector<sort> sorts;
			get_free_vars(exp, sorts);
			expr_ref_vector subst(m);
			subst.reserve(sorts.size());
			for (unsigned i = 0; i < sorts.size(); ++i) {
                if (sorts[i]) {
                    subst[i] = app->get_arg(i);
                }
			}
			return apply_subst(exp, subst);
		}

		expr_ref ground(expr_ref const& exp, char const* prefix) {
			ptr_vector<sort> sorts;
			get_free_vars(exp, sorts);
			expr_ref_vector subst(m);
			subst.reserve(sorts.size());
			for (unsigned i = 0; i < sorts.size(); ++i) {
                if (sorts[i]) {
                    subst[i] = m.mk_fresh_const(prefix, sorts[i]);
                }
			}
			return apply_subst(exp, subst);
		}

		bool check_solution() {
            smt_params new_param;
            smt::kernel solver(m, new_param);
			model_ref& md = get_model();
			for (unsigned i = 0; i < m_rule2info.size(); ++i) {
				rule* r = m_rule2info[i].m_rule;
                if (!r) {
                    // TBD: pay attention to template rules?
                    continue;
                }
                unsigned usz = r->get_uninterpreted_tail_size();
                unsigned tsz = r->get_tail_size();
                expr_ref body_exp = mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz));
				for (unsigned i = 0; i < usz; ++i) {
					body_exp = mk_conj(body_exp, model_eval_app(md, r->get_tail(i)));
				}
				expr_ref head_exp(m);
				if (!m_func_decl2info[r->get_decl()]->m_is_output_predicate) {
					head_exp = model_eval_app(md, r->get_head());
				}
                else {
                    head_exp = m.mk_false();
                }

				scoped_push push(solver);
				solver.assert_expr(ground(mk_conj(body_exp, mk_not(head_exp)), "c"));
				if (solver.check() != l_false) {
					return false;
				}
			}
			return true;
		}

        bool find_solution(unsigned refine_count, acr_error& error) {
            m_node_worklist.reset();

            try {
                // initial abstract inference
                STRACE("predabst", tout << "Performing initial inference\n";);
                for (unsigned r_id = 0; !m_cancel && r_id < m_rule2info.size(); ++r_id) {
                    if (m_rule2info[r_id].m_instance_info.uninterpreted_tail_size() == 0) {
                        initialize_abs(r_id);
                    }
                }

                // process worklist
                unsigned infer_count = 0;
                while (!m_cancel && !m_node_worklist.empty()) {
                    m_stats.m_num_predabst_iterations++;

                    STRACE("predabst", print_inference_state(tout, refine_count, infer_count););
                    unsigned current_id = *m_node_worklist.begin();
                    m_node_worklist.remove(current_id);
                    inference_step(current_id);
                    infer_count++;

                    if ((m_fp_params.max_predabst_iterations() > 0) &&
                        (m_stats.m_num_predabst_iterations >= m_fp_params.max_predabst_iterations())) {
                        m_cancel = true;
                    }
                }

#ifdef Z3DEBUG
				if (!m_cancel && !check_solution()) {
					throw default_exception("check_solution failed");
				}
#endif

                // We managed to find a solution.
                return true;
            }
            catch (acr_error const& error2) {
                // We failed to find a solution.
                error = error2;
                return false;
            }
        }

        void initialize_abs(unsigned r_id) {
            cart_pred_abst_rule(r_id);
        }

        void inference_step(unsigned node_id) {
            // Find all rules whose body contains the func_decl of the new node.
            func_decl* fdecl = m_node2info[node_id].m_func_decl;
            uint_set const& rules = m_func_decl2info[fdecl]->m_users;
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
                    // Try all possible combinations of nodes that can be used
                    // with this rule, assuming that the new node is used at
                    // this position.
                    cart_pred_abst_rule(*r_id, *current_pos, node_id);
                }
            }
        }

        uint_set get_rule_body_positions(rule* r, func_decl* fdecl) {
            uint_set positions;
            for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                if (r->get_decl(i) == fdecl) {
                    positions.insert(i);
                }
            }
            return positions;
        }

        // This is implementing the "abstract inference rules" from Figure 2 of "synthesizing software verifiers from proof rules".
        // With no 3rd argument, rule Rinit is applied; otherwise rule Rstep is applied.
        void cart_pred_abst_rule(unsigned r_id, unsigned fixed_pos = 0, unsigned fixed_node = NON_NODE) {
            rule_instance_info const& info = m_rule2info[r_id].m_instance_info;
            CASSERT("predabst", (fixed_node == NON_NODE) || (fixed_pos < info.uninterpreted_tail_size()));

            if (m_rule2info[r_id].m_unsat) {
                STRACE("predabst", tout << "Skipping rule " << r_id << " with unsatisfiable body\n";);
                return;
            }

#ifndef PREDABST_ASSERT_EXPR_UPFRONT
            scoped_push _push1(m_solver);
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                m_solver.assert_expr(info.m_body[i]);
            }
#endif

            node_vector nodes;
            expr_ref_vector cond_vars(m); // unused unless PREDABST_ASSERT_EXPR_UPFRONT defined
            vector<unsigned> pos_order = get_rule_pos_order(r_id, fixed_pos);
            cart_pred_abst_rule(r_id, 0, fixed_pos, fixed_node, nodes, cond_vars, pos_order);
        }

        vector<unsigned> get_rule_pos_order(unsigned r_id, unsigned fixed_pos) {
            rule_instance_info const& info = m_rule2info[r_id].m_instance_info;

            std::vector<std::pair<unsigned, unsigned>> pos_counts;
            for (unsigned pos = 0; pos < info.uninterpreted_tail_size(); ++pos) {
                unsigned n = (pos == fixed_pos) ? 1 : m_func_decl2info[m_rule2info[r_id].m_rule->get_decl(pos)]->m_max_reach_nodes.num_elems();
                STRACE("predabst-cprod", tout << "There are " << n << " option(s) for position " << pos << "\n";);
                pos_counts.push_back(std::make_pair(n, pos));
            }

#ifdef PREDABST_ORDER_CARTPROD_CHOICES
            std::sort(pos_counts.begin(), pos_counts.end());
#endif

            vector<unsigned> pos_order;
            for (unsigned i = 0; i < pos_counts.size(); ++i) {
                pos_order.push_back(pos_counts[i].second);
            }
            return pos_order;
        }

        bool is_implied(expr* e, rule_instance_info const& info, expr_ref_vector& cond_vars) {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            cond_vars.push_back(e);
            m_stats.m_num_solver_check_head_invocations++;
            lbool result = info.m_rule_solver->check(cond_vars.size(), cond_vars.c_ptr());
            cond_vars.pop_back();
#else
            scoped_push _push2(m_solver);
            m_stats.m_num_solver_assert_invocations++;
            m_solver.assert_expr(e);
            m_stats.m_num_solver_check_head_invocations++;
            lbool result = m_solver.check();
#endif
            return (result == l_false);
        }

#ifndef PREDABST_COMPLETE_CUBE
        void build_cube(cube_t& cube, expr_ref_vector const& es, vector<pred_info> const& preds, vector<unsigned> const& pred_idxs, rule_instance_info const& info, expr_ref_vector& cond_vars) {
            for (unsigned i = 0; i < pred_idxs.size(); ++i) {
                unsigned idx = pred_idxs[i];
                CASSERT("predabst", !cube[idx]);
                if (is_implied(es[idx], info, cond_vars)) {
                    cube[idx] = true;
                }
                else {
                    build_cube(cube, es, preds, preds[idx].m_implied, info, cond_vars);
                }
            }
        }
#endif

        void cart_pred_abst_rule(unsigned r_id, unsigned pos_idx, unsigned fixed_pos, unsigned fixed_node, node_vector& nodes, expr_ref_vector& cond_vars, vector<unsigned> const& pos_order) {
            rule_instance_info const& info = m_rule2info[r_id].m_instance_info;

            if (pos_idx < info.uninterpreted_tail_size()) {
                unsigned pos = pos_order[pos_idx];

                node_set fixed_node_singleton;
                fixed_node_singleton.insert(fixed_node);

                rule* r = m_rule2info[r_id].m_rule;
                CASSERT("predabst", r);
                node_set pos_nodes = (pos == fixed_pos) ? fixed_node_singleton : m_func_decl2info[r->get_decl(pos)]->m_max_reach_nodes; // make a copy, to prevent it from changing while we iterate over it
                for (node_set::iterator pos_node = pos_nodes.begin(), pos_node_end = pos_nodes.end(); pos_node != pos_node_end; ++pos_node) {
                    if ((*pos_node > fixed_node) || ((pos > fixed_pos) && (*pos_node == fixed_node))) {
                        // Don't use any nodes newer than the fixed node; we'll have a chance to use newer nodes when they are taken off the worklist later.
                        // Furthermore, don't use the fixed node further along that the fixed position; we'll have a chance to use it in both places when the fixed position advances.
                        // Note that iterating over the max_reach_nodes set return nodes in ascending order, so we can bail out here.
                        break;
                    }

                    nodes.push_back(*pos_node);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    unsigned num_cond_vars_pushed = 0;
#else
                    scoped_push _push1(m_solver);
#endif
                    cube_t const& pos_cube = m_node2info[*pos_node].m_cube;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    expr_ref_vector const& body_pred_cond_vars = info.m_body_pred_cond_vars[pos];
                    unsigned num_preds = body_pred_cond_vars.size();
#else
                    expr_ref_vector const& body_preds = info.m_body_preds[pos];
                    unsigned num_preds = body_preds.size();
#endif
                    CASSERT("predabst", num_preds == pos_cube.size());
                    for (unsigned i = 0; i < num_preds; ++i) {
                        if (pos_cube[i]) {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                            num_cond_vars_pushed++;
                            cond_vars.push_back(body_pred_cond_vars[i]);
#else
                            m_stats.m_num_solver_assert_invocations++;
                            m_solver.assert_expr(body_preds[i]);
#endif
                        }
                    }

                    m_stats.m_num_solver_check_body_invocations++;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    lbool result = info.m_rule_solver->check(cond_vars.size(), cond_vars.c_ptr());
#else
                    lbool result = m_solver.check();
#endif
                    if (result == l_false) {
                        // unsat body
                        STRACE("predabst", tout << "Applying rule " << r_id << " to nodes (" << nodes << "...) failed\n";); // >>> note: order of nodes is not as expected!
                        m_stats.m_num_rules_failed++;
                    }
                    else {
                        cart_pred_abst_rule(r_id, pos_idx + 1, fixed_pos, fixed_node, nodes, cond_vars, pos_order);
                    }

#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    for (unsigned i = 0; i < num_cond_vars_pushed; ++i) {
                        cond_vars.pop_back();
                    }
#endif
                    nodes.pop_back();
                }
            }
            else {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                CASSERT("predabst", info.m_rule_solver->check(cond_vars.size(), cond_vars.c_ptr()) != l_false);
#else
                CASSERT("predabst", m_solver.check() != l_false);
#endif

                // collect abstract cube
                cube_t cube = cart_pred_abst_cube(r_id, info, cond_vars);
                STRACE("predabst", tout << "Applying rule " << r_id << " to nodes (" << nodes << ") succeeded, with cube [" << cube << "]\n";);
                m_stats.m_num_rules_succeeded++;

                // add and check the node
                check_node_property(add_node(m_rule2info[r_id].m_func_decl, cube, r_id, nodes));
            }
        }

        cube_t cart_pred_abst_cube(unsigned r_id, rule_instance_info const& info, expr_ref_vector& cond_vars) {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            expr_ref_vector const& es = info.m_head_pred_cond_vars;
#else
            expr_ref_vector const& es = info.m_head_preds;
#endif
            unsigned num_preds = es.size();
            cube_t cube;
            cube.resize(num_preds);
#ifdef PREDABST_COMPLETE_CUBE
            for (unsigned i = 0; i < num_preds; ++i) {
                cube[i] = is_implied(es.get(i), info, cond_vars);
            }
#else
            func_decl* fdecl = m_rule2info[r_id].m_func_decl;
            build_cube(cube, es, m_func_decl2info[fdecl]->m_preds, m_func_decl2info[fdecl]->m_root_preds, info, cond_vars);
#endif
            return cube;
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
            cube_t const& cube = m_node2info[id].m_cube;

            expr_ref_vector const& vars = m_func_decl2info[fdecl]->m_vars;
            vector<pred_info> const& preds = m_func_decl2info[fdecl]->m_preds;
            expr_ref expr = cube_to_formula(cube, preds);
            expr_ref_vector args = get_fresh_args(fdecl, "s");
            expr_ref to_rank = apply_subst(expr, build_subst(vars, args));

            return well_founded(args, to_rank, NULL, NULL);
        }

        unsigned add_node(func_decl* fdecl, cube_t const& cube, unsigned r_id, node_vector const& nodes = node_vector()) {
            // first fixpoint check combined with maximality maintainance
            node_set& sym_nodes = m_func_decl2info[fdecl]->m_max_reach_nodes;
            node_vector old_lt_nodes;
            for (node_set::iterator it = sym_nodes.begin(), end = sym_nodes.end(); it != end; ++it) {
                cube_t const& old_cube = m_node2info[*it].m_cube;
                // if cube implies existing cube then nothing to add
                if (cube_leq(cube, old_cube, fdecl)) {
                    STRACE("predabst", tout << "New node is subsumed by node " << *it << " with cube [" << old_cube << "]\n";);
                    CASSERT("predabst", old_lt_nodes.size() == 0);
                    m_stats.m_num_nodes_suppressed++;
                    return NON_NODE;
                }
                // stronger old cubes will not be considered maximal
                if (cube_leq(old_cube, cube, fdecl)) {
                    STRACE("predabst", tout << "New node subsumes node " << *it << " with cube [" << old_cube << "]\n";);
                    old_lt_nodes.push_back(*it);
                }
            }
            // (no???) fixpoint reached since didn't return
            // remove subsumed maximal nodes
            for (node_vector::iterator it = old_lt_nodes.begin(), end = old_lt_nodes.end(); it != end; ++it) {
                m_stats.m_num_nodes_subsumed++;
                sym_nodes.remove(*it);
                m_node_worklist.remove(*it); // removing non-existent element is ok
            }
            // no fixpoint reached hence create new node
            m_stats.m_num_nodes_created++;
            unsigned added_id = m_node2info.size();
            sym_nodes.insert(added_id);
            m_node_worklist.insert(added_id);
            m_node2info.push_back(node_info(fdecl, cube, r_id, nodes));
            STRACE("predabst", tout << "Added node " << added_id << " for " << fdecl->get_name() << "\n";);
            return added_id;
        }

        bool refine_predicates(core_tree_info const& core_info) {
            refine_cand_info refine_info;
            core_clauses clauses = mk_core_clauses(core_info, refine_info);
            vector<refine_pred_info> interpolants = solve_core_clauses(clauses);
            return refine_preds(refine_info, interpolants);
        }

        bool should_refine_predicates_not_wf(unsigned node_id, core_tree_wf_info& core_wf_info) {
            expr_ref_vector args = get_fresh_args(m_node2info[node_id].m_func_decl, "s");
            expr_ref to_wf = mk_core_tree_wf(node_id, args, core_wf_info.m_refine_info);
            quantifier_elimination(args, to_wf);
            return well_founded(args, to_wf, &core_wf_info.m_bound, &core_wf_info.m_decrease);
        }

        bool refine_predicates_not_wf(core_tree_wf_info const& core_wf_info) {
            vector<refine_pred_info> interpolants;
            interpolants.push_back(refine_pred_info(core_wf_info.m_bound, get_all_vars(core_wf_info.m_bound)));
            interpolants.push_back(refine_pred_info(core_wf_info.m_decrease, get_all_vars(core_wf_info.m_decrease)));
            return refine_preds(core_wf_info.m_refine_info, interpolants);
        }

        bool refine_preds(refine_cand_info const& refine_info, vector<refine_pred_info> const& interpolants) {
            for (unsigned i = 0; i < interpolants.size(); ++i) {
                STRACE("predabst", tout << "Interpolant " << i << ": "; print_interpolant(tout, interpolants.get(i)););
            }
            unsigned new_preds_added = 0;
            for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                func_decl *fdecl = m_func_decls.get(i);
                vector<expr_ref_vector> const& rel_info = refine_info.get(fdecl);
                for (unsigned j = 0; j < rel_info.size(); ++j) {
                    for (unsigned k = 0; k < interpolants.size(); ++k) {
                        new_preds_added += get_interpolant_pred(fdecl, rel_info.get(j), interpolants.get(k));
                    }
                }
            }
            return (new_preds_added > 0);
        }

        static bool is_args_pred(expr_ref_vector const& args, expr_ref_vector const& vars) {
            return is_subset(vars, args);
        }

        static bool contains_pred(vector<pred_info> const& preds, expr_ref const& pred) {
            for (vector<pred_info>::const_iterator it = preds.begin(),
                end = preds.end(); it != end; ++it) {
                if (it->m_pred == pred) {
                    return true;
                }
            }
            return false;
        }

        unsigned get_interpolant_pred(func_decl* fdecl, expr_ref_vector const& args, refine_pred_info const& interpolant) {
            expr_ref_vector const& vars = m_func_decl2info[fdecl]->m_vars;
            vector<pred_info>& preds = m_func_decl2info[fdecl]->m_preds;

            unsigned new_preds_added = 0;
            if (is_args_pred(args, interpolant.m_pred_vars)) {
                expr_ref const& in_pred = interpolant.m_pred;
                expr_ref in_pred2(replace_pred(args, vars, in_pred), m);
                if (!contains_pred(preds, in_pred2)) {
                    STRACE("predabst", tout << "Found new predicate " << mk_pp(in_pred2, m) << " for " << fdecl->get_name() << "\n";);
                    preds.push_back(pred_info(in_pred2));
                    ++new_preds_added;
                }
                else {
                    STRACE("predabst", tout << "Predicate " << mk_pp(in_pred2, m) << " for " << fdecl->get_name() << " is already present\n";);
                }
            }
            STRACE("predabst", tout << "Found " << new_preds_added << " new predicates for " << fdecl->get_name() << " using "; print_expr_ref_vector(tout, args, false); tout << ", "; print_interpolant(tout, interpolant););
            return new_preds_added;
        }

        bool refine_templates(acr_error error) {
            expr_ref_vector args = get_fresh_args(m_node2info[error.m_node].m_func_decl, "r");
            expr_ref cs = mk_leaf(error.m_node, args);

            expr_ref to_solve(m);
            if (error.m_kind == reached_query) {
                STRACE("predabst", tout << "Refining templates (reached query)\n";);
                to_solve = template_constraint_reached_query(cs);
            }
            else {
                CASSERT("predabst", error.m_kind == not_wf);
                STRACE("predabst", tout << "Refining templates (not well-founded)\n";);
                to_solve = template_constraint_not_wf(args, cs);
            }

            m_template.constrain_templates(to_solve);
            return m_template.instantiate_templates();
        }

        expr_ref template_constraint_reached_query(expr_ref cs) {
            return expr_ref(m.mk_not(cs), m);
        }

        expr_ref template_constraint_not_wf(expr_ref_vector const& args, expr_ref cs) {
            quantifier_elimination(args, cs);
            expr_ref bound(m);
            expr_ref decrease(m);
            well_founded_bound_and_decrease(args, bound, decrease);
            return expr_ref(m.mk_or(m.mk_not(cs), m.mk_and(bound, decrease)), m);
        }

        bool mk_core_tree(unsigned node_id, core_tree_info &core_info) {
            smt_params new_param;
            smt::kernel solver(m, new_param);
            unsigned& root_name = core_info.m_root_name;
            expr_ref_vector& root_args = core_info.m_root_args;
            core_tree& core = core_info.m_core;

            struct todo_item {
                unsigned        m_name;
                expr_ref_vector m_args;
                todo_item(unsigned name, expr_ref_vector const& args) :
                    m_name(name),
                    m_args(args) {}
            };
            vector<todo_item> todo;

            root_args.append(get_fresh_args(m_node2info[node_id].m_func_decl, "r"));
            root_name = core.size();
            core.push_back(core_tree_node(node_id));
            todo.push_back(todo_item(root_name, root_args));

            while (!todo.empty()) {
                todo_item item = todo.back();
                todo.pop_back();

                unsigned name = item.m_name;
                expr_ref_vector const& args = item.m_args;

                unsigned n_id = core[name].m_node_id;
                node_info const& node = m_node2info[n_id];
                rule* r = m_rule2info[node.m_parent_rule].m_rule;
                if (r) {
                    STRACE("predabst", tout << "mk_core_tree: node " << n_id << "; " << node.m_func_decl->get_name() << "#" << name << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a rule application\n";);
                    expr_ref_vector rule_subst = get_subst_vect(r, args, "s");
                    unsigned usz = r->get_uninterpreted_tail_size();
                    unsigned tsz = r->get_tail_size();
                    for (unsigned i = usz; i < tsz; ++i) {
                        app_ref as = apply_subst(r->get_tail(i), rule_subst);
                        STRACE("predabst", tout << "  requires " << mk_pp(as, m) << "\n";);
                        solver.assert_expr(as);
                        if (solver.check() == l_false) {
                            STRACE("predabst", tout << "Last constraint is unsatisfiable\n";);
                            core_info.m_last_name = name;
                            core_info.m_last_pos = i;
                            return true;
                        }
                    }
                    for (unsigned i = 0; i < usz; ++i) { // Each iteration corresponds to an in-arrow to this node.
                        app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                        expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                        unsigned qname = core.size();
                        core.push_back(core_tree_node(node.m_parent_nodes[i]));
                        todo.push_back(todo_item(qname, qargs));
                        core[name].m_names.push_back(qname);
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_core_tree: node " << n_id << "; " << node.m_func_decl->get_name() << "#" << name << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a template\n";);
                    expr_ref temp_body(m);
                    expr_ref_vector temp_vars(m);
                    m_template.get_template(m_rule2info[node.m_parent_rule].m_template_id, temp_body, temp_vars);
                    expr_ref_vector temp_subst = build_subst(temp_vars, args);
                    temp_body = apply_subst(temp_body, temp_subst);
                    expr_ref_vector inst_body_terms = get_conj_terms(temp_body);
                    for (unsigned i = 0; i < inst_body_terms.size(); ++i) {
                        STRACE("predabst", tout << "  requires " << mk_pp(inst_body_terms.get(i), m) << "\n";);
                        solver.assert_expr(inst_body_terms.get(i));
                        if (solver.check() == l_false) {
                            STRACE("predabst", tout << "Last constraint is unsatisfiable\n";);
                            core_info.m_last_name = name;
                            core_info.m_last_pos = i;
                            return true;
                        }
                    }
                }
            }

            return false;
        }

        core_clauses mk_core_clauses(core_tree_info const& core_info, refine_cand_info &refine_info) {
            core_clauses clauses;

            unsigned root_name = core_info.m_root_name;
            expr_ref_vector const& root_args = core_info.m_root_args;
            unsigned last_name = core_info.m_last_name;
            unsigned last_pos = core_info.m_last_pos;
            core_tree const& core = core_info.m_core;

            struct todo_item {
                unsigned        m_name;
                expr_ref_vector m_args;
                todo_item(unsigned name, expr_ref_vector const& args) :
                    m_name(name),
                    m_args(args) {}
            };
            vector<todo_item> todo;

            todo.push_back(todo_item(root_name, root_args));

            bool found_last = false;
            while (!found_last) {
                CASSERT("predabst", !todo.empty());
                todo_item item = todo.back();
                todo.pop_back();

                unsigned name = item.m_name;
                expr_ref_vector const& args = item.m_args;

                if (name == last_name) {
                    found_last = true;
                }

                expr_ref cs(m);

                node_info const& node = m_node2info[core[name].m_node_id];
                vector<unsigned> const& names = core[name].m_names;
                refine_info.insert(node.m_func_decl, args);

                rule* r = m_rule2info[node.m_parent_rule].m_rule;
                if (r) {
                    STRACE("predabst", tout << "mk_core_clauses: " << node.m_func_decl->get_name() << "#" << name << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a rule application\n";);
                    expr_ref_vector rule_subst = get_subst_vect(r, args, "s");
                    unsigned usz = r->get_uninterpreted_tail_size();
                    unsigned tsz = r->get_tail_size();
                    if (found_last) {
                        cs = apply_subst(mk_conj(expr_ref_vector(m, last_pos - usz + 1, r->get_expr_tail() + usz)), rule_subst);
                    }
                    else {
                        cs = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
                    }
                    for (unsigned i = 0; i < names.size(); ++i) {
                        app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                        expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                        todo.push_back(todo_item(names.get(i), qargs));
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_core_clauses: " << node.m_func_decl->get_name() << "#" << name << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a template\n";);
                    if (found_last) {
                        expr_ref inst_body(m);
                        expr_ref_vector inst_vars(m);
                        m_template.get_template_instance(m_rule2info[node.m_parent_rule].m_template_id, inst_body, inst_vars);
                        expr_ref_vector inst_body_terms = get_conj_terms(inst_body);
                        cs = mk_conj(expr_ref_vector(m, last_pos + 1, inst_body_terms.c_ptr()));
                    }
                    else {
                        expr_ref temp_body(m);
                        expr_ref_vector temp_vars(m);
                        m_template.get_template(m_rule2info[node.m_parent_rule].m_template_id, temp_body, temp_vars);
                        expr_ref_vector temp_subst = build_subst(temp_vars, args);
                        temp_body = apply_subst(temp_body, temp_subst);
                        expr_ref inst_body(m);
                        m_template.get_modref()->eval(temp_body, inst_body);
                        cs = inst_body;
                    }
                }

                if (args.size() > 0 || !m.is_true(cs)) {
                    STRACE("predabst", tout << "  adding clause " << node.m_func_decl->get_name() << "#" << name << "("; print_expr_ref_vector(tout, args, false); tout << ") :- " << mk_pp(cs, m) << "\n";);
                    clauses.push_back(core_clause(name, args, cs));
                }
            }

            return clauses;
        }

        vector<refine_pred_info> solve_core_clauses(core_clauses const& clauses) {
            vector<refine_pred_info> interpolants;

            core_clauses::const_iterator end = clauses.end();
            end--;
            for (int i = clauses.size() - 1; i >= 1; i--) {
                int j = clauses.size() - 1;
                core_clauses::const_iterator end2 = end;

                expr_ref fmlA(m.mk_true(), m);
                for (; j >= i; j--, end2--) {
                    fmlA = mk_conj(fmlA, end2->m_body);
                }

                core_clauses::const_iterator end4 = end2;
                end4++;
                expr_ref_vector vars = end4->m_args;

                expr_ref fmlB(m.mk_true(), m);
                for (; j >= 0; j--, end2--) {
                    fmlB = mk_conj(fmlB, end2->m_body);
                }

                expr_ref fmlQ_sol(m);
                if (interpolate(vars, fmlA, fmlB, fmlQ_sol)) {
                    interpolants.push_back(refine_pred_info(fmlQ_sol, get_all_vars(fmlQ_sol)));
                }
            }

            return interpolants;
        }

        expr_ref mk_core_tree_wf(unsigned root_n_id, expr_ref_vector const& root_args, refine_cand_info& refine_info) {
            expr_ref_vector to_wfs(m);

            struct todo_item {
                unsigned        m_node_id;
                expr_ref_vector m_args;
                todo_item(unsigned node_id, expr_ref_vector const& args) :
                    m_node_id(node_id),
                    m_args(args) {}
            };
            vector<todo_item> todo;

            todo.push_back(todo_item(root_n_id, root_args));

            while (!todo.empty()) {
                todo_item item = todo.back();
                todo.pop_back();

                unsigned n_id = item.m_node_id;
                expr_ref_vector const& args = item.m_args;

                expr_ref cs(m);

                node_info const& node = m_node2info[n_id];
                refine_info.insert(node.m_func_decl, args);

                rule* r = m_rule2info[node.m_parent_rule].m_rule;
                if (r) {
                    STRACE("predabst", tout << "mk_core_tree_wf: node " << n_id << "; " << node.m_func_decl->get_name() << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a rule application\n";);
                    expr_ref_vector rule_subst = get_subst_vect(r, args, "s");
                    unsigned usz = r->get_uninterpreted_tail_size();
                    unsigned tsz = r->get_tail_size();
                    cs = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
                    for (unsigned i = 0; i < usz; ++i) {
                        app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                        expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                        todo.push_back(todo_item(node.m_parent_nodes[i], qargs));
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_core_tree_wf: node " << n_id << "; " << node.m_func_decl->get_name() << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a template\n";);
                    expr_ref temp_body(m);
                    expr_ref_vector temp_vars(m);
                    m_template.get_template(m_rule2info[node.m_parent_rule].m_template_id, temp_body, temp_vars);
                    expr_ref_vector temp_subst = build_subst(temp_vars, args);
                    temp_body = apply_subst(temp_body, temp_subst);
                    expr_ref inst_body(m);
                    m_template.get_modref()->eval(temp_body, inst_body);
                    cs = inst_body;
                }

                to_wfs.push_back(cs);
            }

            return mk_conj(to_wfs);
        }

        expr_ref mk_leaf(unsigned root_n_id, expr_ref_vector root_args) {
            expr_ref_vector css(m);

            struct todo_item {
                unsigned        m_n_id;
                expr_ref_vector m_args;
                todo_item(unsigned n_id, expr_ref_vector const& args) :
                    m_n_id(n_id),
                    m_args(args) {}
            };
            vector<todo_item> todo;

            todo.push_back(todo_item(root_n_id, root_args));

            while (!todo.empty()) {
                todo_item item = todo.back();
                todo.pop_back();

                unsigned n_id = item.m_n_id;
                expr_ref_vector const& args = item.m_args;

                expr_ref cs(m);

                node_info const& node = m_node2info[n_id];
                rule* r = m_rule2info[node.m_parent_rule].m_rule;
                if (r) {
                    STRACE("predabst", tout << "mk_leaf: node " << n_id << "; " << node.m_func_decl->get_name() << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a rule application\n";);
                    expr_ref_vector rule_subst = get_subst_vect(r, args, "s");
                    unsigned usz = r->get_uninterpreted_tail_size();
                    unsigned tsz = r->get_tail_size();
                    expr_ref conj = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
                    cs = conj;
                    for (unsigned i = 0; i < usz; ++i) {
                        app_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                        expr_ref_vector qargs(m, qs_i->get_decl()->get_arity(), qs_i->get_args());
                        todo.push_back(todo_item(node.m_parent_nodes[i], qargs));
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_leaf: node " << n_id << "; " << node.m_func_decl->get_name() << "("; print_expr_ref_vector(tout, args, false); tout << ") was generated by a template\n";);
                    cs = m.mk_app(m_node2info[n_id].m_func_decl, args.c_ptr());
                }
                css.push_back(cs);
            }

            return mk_conj(css);
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
                out << "core_name: " << i << ", core_id: " << core[i].m_node_id << ", core_ids: [";
                for (unsigned j = 0; j < core[i].m_names.size(); ++j) {
                    out << " " << core[i].m_names.get(j);
                }
                out << "]\n";
            }
        }

        void print_core_clauses(std::ostream& out, core_clauses const& clauses) const {
            for (unsigned i = 0; i < clauses.size(); ++i) {
                core_clause const& clause = clauses[i];
                out << "clause --> " << clause.m_name << " (";
                print_expr_ref_vector(out, clause.m_args, false);
                out << ") : " << mk_pp(clause.m_body, m) << "\n";
            }
        }

        void print_interpolant(std::ostream& out, refine_pred_info const& interpolant) const {
            out << "pred: " << mk_pp(interpolant.m_pred, m) << ", pred_vars: (";
            print_expr_ref_vector(out, interpolant.m_pred_vars, false);
            out << ")\n";
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
                out << " is used by rules " << it->m_value->m_users << std::endl;
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
            for (unsigned i = 0; i < m_template.get_num_templates(); ++i) {
                rel_template const& temp = m_template.get_template(i);
                out << "    " << i << ": " << mk_pp(temp.m_head, m) << " := " << mk_pp(temp.m_body, m) << std::endl;
            }
            out << "=====================================\n";
        }

#ifndef PREDABST_COMPLETE_CUBE
        void print_preds_forest(std::ostream& out, vector<pred_info> const& preds, vector<unsigned> const& preds_idxs, std::string const& prefix) const {
            for (unsigned i = 0; i < preds_idxs.size(); ++i) {
                unsigned idx = preds_idxs[i];
                out << prefix << mk_pp(preds[idx].m_pred, m) << "\n";
                print_preds_forest(out, preds, preds[idx].m_implied, prefix + "  ");
            }
        }

        void print_preds_forest(std::ostream& out, func_decl* fdecl) const {
            print_preds_forest(out, m_func_decl2info[fdecl]->m_preds, m_func_decl2info[fdecl]->m_root_preds, "");
        }
#endif

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
                for (vector<pred_info>::iterator it2 = it->m_value->m_preds.begin(),
                    end2 = it->m_value->m_preds.end(); it2 != end2; ++it2) {
                    out << it2->m_pred << " ";
                }
                out << std::endl;
            }
            out << "  Template instances:" << std::endl;
            for (unsigned i = 0; i < m_template.get_num_templates(); ++i) {
                rel_template const& instance = m_template.get_template_instance(i);
                out << "    " << i << ": " << mk_pp(instance.m_head, m) << " := " << mk_pp(instance.m_body, m) << std::endl;
            }
            out << "  Instantiated rules:" << std::endl;
            for (unsigned r_id = 0; r_id < m_rule2info.size(); ++r_id) {
                out << "    " << r_id << ":" << std::endl;
                m_rule2info[r_id].m_instance_info.display(out);
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

        void print_statistics(std::ostream& out) const {
            statistics st;
            collect_statistics(st);
            st.display(out);
        }
    };

    predabst::predabst(context& ctx) :
        engine_base(ctx.get_manager(), "predabst"),
        m_ctx(ctx),
        m_imp(alloc(imp, ctx.get_manager(), ctx.get_params())) {
    }
    predabst::~predabst() {
        dealloc(m_imp);
    }
    lbool predabst::query(expr* query) {
        m_ctx.ensure_opened();
        rule_set& rules = m_ctx.get_rules();
        m_ctx.get_rule_manager().mk_query(query, rules);
        return m_imp->query(rules);
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
        for (unsigned i = 1; i < size; ++i) {
            out << "," << v[i];
        }
    }
    return out;
}
