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
        typedef std::pair<expr* const*, expr_ref_vector*> vars_preds;
        typedef obj_map<func_decl, vars_preds> func_decl2vars_preds;
        typedef obj_map<func_decl, uint_set> func_decl2rule_set;
        typedef obj_map<func_decl, node_set> func_decl2node_set;
        typedef std::pair<unsigned, func_decl*> name2symbol;
        typedef std::map<unsigned, std::pair<std::pair<unsigned, vector<unsigned> >, vector<unsigned> > > core_tree;

        struct rule_info {
            expr_ref                m_body;
            expr_ref_vector         m_head_preds;
            vector<expr_ref_vector> m_body_preds;
            rule_info(expr_ref const& body) :
                m_body(body),
                m_head_preds(body.m()) {}
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

        context&               m_ctx;         // main context where (fixedpoint) constraints are stored.
        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        rule_manager&          rm;            // context with utilities for fixedpoint rules.
        smt_params             m_fparams;     // parameters specific to smt solving
        smt::kernel            m_solver;      // basic SMT solver class
        var_subst              m_var_subst;   // substitution object. It gets updated and reset.
        volatile bool          m_cancel;      // Boolean flag to track external cancelation.
        stats                  m_stats;       // statistics information specific to the predabst module.

        rel_template_suit      m_template;
        func_decl_ref_vector   m_func_decls;
        func_decl2vars_preds   m_func_decl2vars_preds;

        func_decl2rule_set     m_func_decl2rules;
        func_decl2node_set     m_func_decl2max_reach_node_set;
        vector<rule_info>      m_rule2info;
        vector<node_info>      m_node2info;
        node_set               m_node_worklist;

        typedef enum { reached_query, not_wf } acr_error_kind;

        struct acr_error {
            unsigned       m_node;
            acr_error_kind m_kind;
            acr_error(unsigned node, acr_error_kind kind) :
                m_node(node),
                m_kind(kind) {}
        };

        struct core_tree_info {
            unsigned            m_root_id;
            unsigned            m_last_name;
            unsigned            m_last_node_tid;
            unsigned            m_pos;
            vector<name2symbol> m_name_map;
            core_tree           m_core;
            core_tree_info() {}
            core_tree_info(unsigned root_id, unsigned last_name, unsigned last_node_tid, unsigned pos, vector<name2symbol> const& name_map, core_tree const& core) :
                m_root_id(root_id),
                m_last_name(last_name),
                m_last_node_tid(last_node_tid),
                m_pos(pos),
                m_name_map(name_map),
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
            for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(),
                end = m_func_decl2vars_preds.end(); it != end; ++it) {
                dealloc(it->m_value.second);
            }
        }

        lbool query(expr* query) {
            STRACE("predabst", tout << "Query expression " << mk_pp(query, m) << "\n";);
            m_ctx.ensure_opened();
            rule_set& rules = m_ctx.get_rules();
            STRACE("predabst", tout << "Before making the query:\n"; rules.display(tout););
            rm.mk_query(query, rules);
            STRACE("predabst", tout << "After making the query:\n"; rules.display(tout););

            // Some of the rules are actually declarations of predicate lists,
            // templates and extra constraints on templates.  Find these, and
            // remove them from the rule set.
            ptr_vector<rule> to_delete;
            for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                if (is_predicate_list(r)) {
                    collect_predicate_list(r);
                    to_delete.push_back(r);
                }
                else if (is_template(r)) {
                    collect_template(r);
                    to_delete.push_back(r);
                }
                else if (is_template_extra(r)) {
                    collect_template_extra(r);
                    to_delete.push_back(r);
                }
            }

            for (unsigned i = 0; !m_cancel && i < to_delete.size(); ++i) {
                rules.del_rule(to_delete[i]);
            }

            STRACE("predabst", tout << "After extracting predicates and templates:\n"; rules.display(tout););
            m_template.init_template_instantiate();
            return abstract_check_refine(rules);
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
            // reachable predicates are concretized
            for (func_decl2node_set::iterator
                it_decl = m_func_decl2max_reach_node_set.begin(),
                end_decl = m_func_decl2max_reach_node_set.end();
                it_decl != end_decl; ++it_decl) {
                if (it_decl->m_key->get_arity() == 0) {
                    md->register_decl(it_decl->m_key, m.mk_true());
                }
                else {
                    vars_preds vp;
                    expr_ref e(m);
                    if (m_func_decl2vars_preds.find(it_decl->m_key, vp)) {
                        expr_ref_vector disj(m);
                        expr_ref_vector const& preds = *vp.second;
                        for (node_set::iterator it_node = it_decl->m_value.begin(),
                            end_node = it_decl->m_value.end(); it_node != end_node;
                            ++it_node) {
                            cube_t const& cube = m_node2info[*it_node].m_cube;
                            expr_ref_vector conj(m);
                            for (unsigned i = 0; i < cube.size(); ++i) {
                                if (cube[i]) {
                                    conj.push_back(preds[i]);
                                }
                            }
                            disj.push_back(mk_conj(conj));
                        }
                        e = mk_disj(disj);
                    }
                    else {
                        e = m.mk_true();
                    }
                    func_interp* fi = alloc(func_interp, m, it_decl->m_key->get_arity());
                    fi->set_else(e);
                    md->register_decl(it_decl->m_key, fi);
                }
            }
            func_decl_set false_func_decls;
            // unreachable body predicates are false
            for (func_decl2rule_set::iterator it = m_func_decl2rules.begin(),
                end = m_func_decl2rules.end(); it != end; ++it) {
                if (!m_func_decl2max_reach_node_set.contains(it->m_key)) {
                    false_func_decls.insert(it->m_key);
                }
            }
            // unreachable head predicates are false
            rule_set const& rules = m_ctx.get_rules();
            for (rule_set::iterator it = rules.begin(), end = rules.end(); it != end;
                ++it) {
                func_decl* head_decl = (*it)->get_decl();
                if (rules.is_output_predicate(head_decl)) {
                    continue;
                }
                if (!m_func_decl2max_reach_node_set.contains(head_decl)) {
                    false_func_decls.insert(head_decl);
                }
            }
            for (func_decl_set::iterator it = false_func_decls.begin(),
                end = false_func_decls.end(); it != end; ++it) {
                func_decl* d = *it;
                if (d->get_arity() == 0) {
                    md->register_decl(d, m.mk_false());
                }
                else {
                    func_interp* fi = alloc(func_interp, m, d->get_arity());
                    fi->set_else(m.mk_false());
                    md->register_decl(d, fi);
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
        expr_ref_vector build_subst(unsigned n, expr* const* vars, expr* const* exprs) {
            expr_ref_vector inst(m);
            inst.reserve(n); // note that this is not necessarily the final size of inst
            for (unsigned i = 0; i < n; ++i) {
                CASSERT("predabst", is_var(vars[i])); // fails if vars[i] is a constant!  This can only happen when there was no predicate list, and so we inserted an empty list above, but when the arguments to the predicate we inserted were not a set of distinct variables
                unsigned idx = to_var(vars[i])->get_idx();
                if (idx >= inst.size()) {
                    inst.resize(idx + 1);
                }
                inst[idx] = exprs[i];
            }
            return inst;
        }

        bool is_predicate_list(rule const* r) const {
            return r->get_decl()->get_name().str().substr(0, 8) == "__pred__";
        }

        void collect_predicate_list(rule const* r) {
            CASSERT("predabst", is_predicate_list(r));
            // r is a rule of the form:
            //   p1 AND ... AND pN => __pred__SUFFIX
            // Treat p1...pN as initial predicates for query symbol SUFFIX.
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            STRACE("predabst", tout << "Found predicate list for query symbol " << suffix << " with args "; print_expr_ref_vector(tout, expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args())););

            func_decl* suffix_decl = m.mk_func_decl(
                suffix,
                head_decl->get_arity(),
                head_decl->get_domain(),
                head_decl->get_range());
            if (m_func_decls.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found multiple predicate lists for " << suffix << "\n";);
                throw default_exception("found multiple predicate lists for " + suffix.str());
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: predicate list for " << suffix << " has an uninterpreted tail\n";);
                throw default_exception("predicate list for " + suffix.str() + " has an uninterpreted tail");
            }

            // Add SUFFIX to m_func_decls.
            m_func_decls.push_back(suffix_decl);

            // Add SUFFIX -> p1..pN to m_func_decl2vars_preds.
            expr_ref_vector* preds = alloc(expr_ref_vector, m);
            preds->reserve(r->get_tail_size());
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                STRACE("predabst", tout << "  predicate " << i << ": " << mk_pp(r->get_tail(i), m) << "\n";);
                (*preds)[i] = r->get_tail(i);
            }
            m_func_decl2vars_preds.insert(suffix_decl, std::make_pair(r->get_head()->get_args(), preds));
        }

        bool is_template(rule const* r) const {
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

            CASSERT("predabst", head_decl->get_arity() >= m_template.get_params_count());
            unsigned new_arity = head_decl->get_arity() - m_template.get_params_count();
            func_decl* suffix_decl = m.mk_func_decl(
                suffix,
                new_arity,
                head_decl->get_domain(),
                head_decl->get_range());
            if (m_template.get_names().contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found multiple templates for " << suffix << "\n";);
                throw default_exception("found multiple templates for " + suffix.str());
            }

            if (r->get_tail_size() != 1) {
                STRACE("predabst", tout << "Error: template tail size is " << r->get_tail_size() << " but should be 1\n";);
                throw default_exception("template for " + suffix.str() + " has tail of length != 1");
            }

            expr_ref_vector temp_subst(m);
            temp_subst.reserve(new_arity);
            for (unsigned i = 0; i < new_arity; ++i) {
                temp_subst[i] = m.mk_fresh_const("v", arith_util(m).mk_int());
            }
            app* suffix_app = m.mk_app(suffix_decl, r->get_head()->get_args());
            expr_ref body1 = apply_subst(r->get_tail(0), m_template.get_params());
            STRACE("predabst", tout << "  template SK: " << mk_pp(suffix_app, m) << "; " << mk_pp(body1, m) << "\n";);
            m_template.process_template_sk(rel_template(suffix_app, body1));

            expr_ref_vector all_subst(temp_subst);
            all_subst.append(m_template.get_params());
            all_subst.reverse();
            app* suffix_app2 = m.mk_app(suffix_decl, new_arity, temp_subst.c_ptr());
            expr_ref body2 = apply_subst(r->get_tail(0), all_subst);
            STRACE("predabst", tout << " template: " << mk_pp(suffix_app2, m) << "; " << mk_pp(body2, m) << "\n";);
            m_template.process_template(suffix_decl, rel_template(suffix_app2, body2), temp_subst);
        }

        bool is_template_extra(rule const* r) const {
            return r->get_decl()->get_name().str().substr(0, 15) == "__temp__extra__";
        }

        void collect_template_extra(rule const* r) {
            CASSERT("predabst", is_template_extra(r));
            // r is a rule of the form:
            //  ??? => __temp__extra__SUFFIX
            // Treat ??? as an extra template constraint for query symbol SUFFIX.
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(15).c_str());
            STRACE("predabst", tout << "Found extra template constraint for query symbol " << suffix << "\n";);

            if (false /* XXX TBD */) {
                STRACE("predabst", tout << "Error: found multiple extra template constraints for " << suffix << "\n";);
                throw default_exception("found multiple extra template constraints for " + suffix.str());
            }

            if (r->get_tail_size() != 1) {
                STRACE("predabst", tout << "Error: extra template constraint tail size is " << r->get_tail_size() << " but should be 1\n";);
                throw default_exception("extra template constraint for " + suffix.str() + " has tail of length != 1");
            }

            expr_ref_vector extra_subst(m);
            extra_subst.reserve(head_decl->get_arity());
            for (unsigned i = 0; i < head_decl->get_arity(); ++i) {
                extra_subst[i] = m.mk_fresh_const("b", arith_util(m).mk_int());
            }
            expr_ref extras = apply_subst(r->get_tail(0), extra_subst);
            STRACE("predabst", tout << "  template extra " << mk_pp(extras, m) << "\n";);
            m_template.process_template_extra(extra_subst, extras);
        }

        lbool abstract_check_refine(rule_set const& rules) {
            // The only things that change on subsequent iterations of this loop are
            // the predicate lists
            // (m_func_decl2vars_preds) and m_template.  The latter can have an
            // effect on the execution of the algorithm via the initial nodes
            // set up by initialize_abs_templates.
            for (unsigned acr_count = 0;; ++acr_count) {
                STRACE("predabst", tout << "=====================================\n";);
                STRACE("predabst", tout << "ACR step : " << acr_count << "\n";);
                STRACE("predabst", tout << "=====================================\n";);

                m_func_decl2rules.reset();
                m_func_decl2max_reach_node_set.reset();
                m_rule2info.reset();
                m_node2info.reset();
                m_node_worklist.reset();

                // for each rule: ground body and instantiate predicates for applications
                for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                    instantiate_rule(rules, i);
                }

                try {
                    // initial abstract inference
                    initialize_abs_templates(rules);
                    for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                        rule* r = rules.get_rule(i);
                        if (r->get_uninterpreted_tail_size() == 0) {
                            initialize_abs(rules, i);
                        }
                    }
                    // process worklist
                    while (!m_cancel && !m_node_worklist.empty()) {
                        TRACE("predabst", print_inference_state(tout););
                        unsigned current_id = *m_node_worklist.begin();
                        m_node_worklist.remove(current_id);
                        inference_step(rules, current_id);
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
                    STRACE("predabst", print_trace(tout, node_id););

                    core_tree_info core_info;
                    if (mk_core_tree(rules, node_id, core_info)) {
                        // The result didn't hold up without abstraction.  We
                        // need to refine the predicates and retry.
                        if (!refine_unreachable(core_info, rules)) {
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
                            result = refine_t_reach(node_id, rules);
                        }
                        else {
                            CASSERT("predabst", exc.m_kind == not_wf);
                            STRACE("predabst", tout << "Refining templates (WF)\n";);
                            result = refine_t_wf(node_id, rules);
                        }

                        if (!result) {
                            STRACE("predabst", tout << "Template refinement unsuccessful: result is UNSAT\n";);
                            return l_true;
                        }

                        STRACE("predabst", tout << "Template refinement successful: retrying\n";);
                    }
                }
            }
        }

        // Sets up m_rule2info and m_func_decl2rules for this iteration of
        // the abstract_check_refine loop, and adds (via app_inst_preds) additional
        // entries to m_func_decl2vars_preds.
        void instantiate_rule(rule_set const& rules, unsigned r_id) {
            rule* r = rules.get_rule(r_id);
            STRACE("predabst", tout << "Instantiating rule " << r_id << "\n"; r->display(m_ctx, tout););

            // prepare grounding substitution
            expr_ref_vector rule_subst = get_subst_vect_free(r, "c");

            // conjoin constraints in rule body
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            STRACE("predabst", tout << "  uninterpreted: " << usz << "; interpreted: " << (tsz - usz) << "\n";);
            expr_ref conj(m.mk_and(tsz - usz, r->get_expr_tail() + usz), m);

            // apply substitution
            STRACE("predabst", tout << "  conj: " << mk_pp(conj, m) << "\n";);
            conj = apply_subst(conj, rule_subst);
            STRACE("predabst", tout << "  conj: " << mk_pp(conj, m) << "\n";);

            // store ground body and instantiations
            rule_info info(conj);
            expr_ref_vector& head_preds = info.m_head_preds;
            vector<expr_ref_vector>& body_preds_vector = info.m_body_preds;

            // store instantiation for non-query head
            if (!rules.is_output_predicate(r->get_decl())) {
                expr_ref_vector heads = app_inst_preds(r->get_head(), rule_subst);
                for (unsigned i = 0; i < heads.size(); ++i) {
                    heads[i] = m.mk_not(heads[i].get());
                }
                STRACE("predabst", tout << "  heads: "; print_expr_ref_vector(tout, heads););
                head_preds.swap(heads);
            }

            // store instantiation for body applications
            for (unsigned i = 0; i < usz; ++i) {
                expr_ref_vector tails = app_inst_preds(r->get_tail(i), rule_subst);
                STRACE("predabst", tout << "  tails[" << i << "]: "; print_expr_ref_vector(tout, tails););
                body_preds_vector.push_back(tails);
            }

            m_rule2info.push_back(info);

            // map body func_decls to rule
            for (unsigned i = 0; i < usz; ++i) {
                STRACE("predabst", tout << "  associating " << mk_pp(r->get_decl(i), m) << " -> rule #" << r_id << "\n";);
                m_func_decl2rules.insert_if_not_there2(r->get_decl(i), uint_set())->get_data().m_value.insert(r_id);
            }
        }

        // ground arguments of appl using subst, and then instantiate each predicate
        // by replacing its free variables with grounded arguments of app
        // Note: subst is vector of constants to substitute for variables 0, 1, ...
        expr_ref_vector app_inst_preds(app* appl, expr_ref_vector const& subst) {
            vars_preds vp;
            if (!m_func_decl2vars_preds.find(appl->get_decl(), vp)) {
                STRACE("predabst", tout << "No predicate list found for " << mk_pp(appl->get_decl(), m) << ": inserting an empty list\n";);
                expr_ref_vector* preds = alloc(expr_ref_vector, m);
                m_func_decl2vars_preds.insert(appl->get_decl(), std::make_pair(appl->get_args(), preds));
                m_func_decls.push_back(appl->get_decl());
                return expr_ref_vector(m);
            }
            expr* const* vars = vp.first;
            expr_ref_vector const& preds = *vp.second;
            if (!preds.size()) {
                return expr_ref_vector(m);
                // XXX This is a hack to work around the incorrect use of appl->get_args() above, to avoid hitting a to_var crash below.
            }
            // ground appl arguments
            expr_ref gappl = apply_subst(appl, subst);
            // instantiation maps preds variables to head arguments
            expr_ref_vector inst = build_subst(to_app(gappl)->get_num_args(), vars, to_app(gappl)->get_args());
            // preds instantiates to inst_preds
            return apply_subst(preds, inst);
        }

        void initialize_abs_templates(rule_set const& rules) {
            unsigned inst_r_id = rules.get_num_rules(); // This is a kind of pseudo- rule id.
            for (unsigned i = 0; i < m_template.get_template_instances().size(); i++) {
                cube_t cube;
                if (cart_temp_pred_abst_rule(m_template.get_template_instances().get(i), m_template.get_orig_templates().get(i), cube)) {
                    add_node(m_template.get_orig_templates().get(i).m_head->get_decl(), cube, inst_r_id, node_vector());
                    inst_r_id++;
                }
                else {
                    // XXX Is this reachable?
                    throw default_exception("m_template.get_template_instances().get(i).m_head");
                }
            }
        }

        void initialize_abs(rule_set const& rules, unsigned r_id) {
            rule* r = rules.get_rule(r_id);
            STRACE("predabst", tout << "Initializing abs using rule " << r_id << "\n"; r->display(m_ctx, tout););

            cube_t cube;
            if (cart_pred_abst_rule(r_id, cube)) {
                check_node_property(rules, add_node(r->get_decl(), cube, r_id));
            }
        }

        void inference_step(rule_set const& rules, unsigned current_id) {
            STRACE("predabst", tout << "Performing inference from node " << current_id << "\n";);
            func_decl* current_func_decl = m_node2info[current_id].m_func_decl;
            func_decl2rule_set::obj_map_entry* e_current_rules = m_func_decl2rules.find_core(current_func_decl);
            if (!e_current_rules) {
                return;
            }
            //get all rules whose body contains the symbol with a new node
            uint_set& current_rules = e_current_rules->get_data().m_value;
            //iterate over each rule
            for (uint_set::iterator r_id = current_rules.begin(), r_id_end = current_rules.end(); r_id != r_id_end; ++r_id) {
                STRACE("predabst", tout << "Attempting to apply rule " << *r_id << "\n";);
                // positions of current_id among body func_decls
                uint_set current_poss;
                rule* r = rules.get_rule(*r_id);
                for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                    if (r->get_decl(i) == current_func_decl) { // XXX we could precompute this set and store it in m_func_decl2rules
                        current_poss.insert(i);
                    }
                }
                STRACE("predabst-cprod", tout << "This node (" << current_id << ") can be used in positions " << current_poss << "\n";);

                node_set current_pos_singleton;
                current_pos_singleton.insert(current_id);

                // current_id is put on each appropriate position
                for (uint_set::iterator current_pos = current_poss.begin(), current_pos_end = current_poss.end(); current_pos != current_pos_end; ++current_pos) {
                    STRACE("predabst-cprod", tout << "Using this node in position " << *current_pos << "\n";);
                    // create set of combinations of nodes to apply the rule
                    vector<node_vector> nodes_set;
                    nodes_set.push_back(node_vector()); // XXX reserve space in this vector, for efficiency?

                    // grow node combinations as cartesian product with nodes at pos
                    for (unsigned pos = 0; pos < r->get_uninterpreted_tail_size(); ++pos) {
                        node_set& pos_nodes = (*current_pos == pos) ? current_pos_singleton : m_func_decl2max_reach_node_set[r->get_decl(pos)];
                        STRACE("predabst-cprod", tout << "There are " << pos_nodes.num_elems() << " option(s) for position " << pos << "\n";);
                        unsigned orig_nodes_set_size = nodes_set.size();
                        // compute cartesian product
                        // first, store the product with first node in place
                        node_set::iterator pos_node = pos_nodes.begin();
                        for (unsigned nodes_set_offset = 0; nodes_set_offset < orig_nodes_set_size; ++nodes_set_offset) {
                            STRACE("predabst-cprod", tout << "Adding " << *pos_node << " to existing set " << nodes_set[nodes_set_offset] << "\n";);
                            nodes_set[nodes_set_offset].push_back(*pos_node);
                        }
                        ++pos_node;
                        // then, product for rest nodes goes into additional vectors
                        for (node_set::iterator pos_node_end = pos_nodes.end(); pos_node != pos_node_end; ++pos_node) {
                            for (unsigned nodes_set_offset = 0; nodes_set_offset < orig_nodes_set_size; ++nodes_set_offset) {
                                STRACE("predabst-cprod", tout << "Using " << *pos_node << " instead of last element of existing set " << nodes_set[nodes_set_offset] << "\n";);
                                node_vector tmp = nodes_set[nodes_set_offset];
                                tmp.back() = *pos_node;
                                nodes_set.push_back(tmp);
                            }
                        }
                    }

                    // apply rule on each node combination
                    for (vector<node_vector>::iterator nodes = nodes_set.begin(), nodes_end = nodes_set.end(); nodes != nodes_end; ++nodes) {
                        CASSERT("predabst", nodes->size() == r->get_uninterpreted_tail_size());
                        cube_t cube;
                        if (cart_pred_abst_rule(*r_id, cube, *nodes)) {
                            check_node_property(rules, add_node(r->get_decl(), cube, *r_id, *nodes));
                        }
                    }
                }

                //STRACE("predabst", tout << "Finished applying rule " << *r_id << "\n";);
            }
            //STRACE("predabst", tout << "Finished performing inference from node " << current_id << "\n";);
        }

        bool cart_temp_pred_abst_rule(rel_template instance, rel_template orig_temp, cube_t& cube) {
            vars_preds vp;
            if (!m_func_decl2vars_preds.find(orig_temp.m_head->get_decl(), vp)) {
                return false;
            }
            expr_ref_vector temp_subst2(m_template.get_temp_subst());
            temp_subst2.reverse();
            scoped_push _push1(m_solver);
            m_solver.assert_expr(instance.m_body);
            if (m_solver.check() == l_false) {
                return false;
            }
            expr_ref_vector const& preds = *vp.second;
            cube.resize(preds.size());
            for (unsigned i = 0; i < preds.size(); ++i) {
                expr_ref subst_pred = apply_subst(preds[i], temp_subst2);
                scoped_push _push2(m_solver);
                m_solver.assert_expr(subst_pred);
                cube[i] = (m_solver.check() == l_true);
            }
            return true;
        }

        // This is implementing the "abstract inference rules" from Figure 2 of "synthesizing software verifiers from proof rules".
        // With no 3rd argument, rule Rinit is applied; otherwise rule Rstep is applied.
        bool cart_pred_abst_rule(unsigned r_id, cube_t& cube, node_vector const& nodes = node_vector()) {
            STRACE("predabst", tout << "Applying rule " << r_id; if (nodes.size()) tout << " to nodes " << nodes; tout << "\n";);
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
                STRACE("predabst", tout << "Rule application failed\n";);
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
            STRACE("predabst", tout << "Rule application succeeded, with cube " << cube << "\n";);
            return true;
        }

        void check_node_property(rule_set const& rules, unsigned id) {
            if (id != NON_NODE && rules.is_output_predicate(m_node2info[id].m_func_decl)) {
                STRACE("predabst", tout << "Reached query symbol " << m_node2info[id].m_func_decl << "\n";);
                throw acr_error(id, reached_query);
            }
            if (id != NON_NODE && is_wf_predicate(m_node2info[id].m_func_decl)) {
                check_well_founded(id);
            }
        }

        bool is_wf_predicate(func_decl const* pred) const {
            return pred->get_name().str().substr(0, 6) == "__wf__";
        }

        void check_well_founded(unsigned r_id) {
            func_decl* pred = m_node2info[r_id].m_func_decl;
            cube_t cube = m_node2info[r_id].m_cube;
            vars_preds vp;
            if (!m_func_decl2vars_preds.find(pred, vp)) {
                return;
            }
            expr* const* vars = vp.first;
            expr_ref_vector const& preds_set = *vp.second;
            expr_ref to_rank(m.mk_true(), m);
            for (unsigned i = 0; i < cube.size(); i++) {
                STRACE("predabst", tout << "check_well_founded: considered cube " << mk_pp(preds_set[i], m) << "\n";);
                if (cube[i]) {
                    to_rank = mk_conj(to_rank, expr_ref(preds_set[i], m));
                    STRACE("predabst", tout << "check_well_founded: used cube " << mk_pp(preds_set[i], m) << "\n";);
                }
            }
            expr_ref_vector subst_vars(m);
            subst_vars.reserve(pred->get_arity());
            for (unsigned i = 0; i < pred->get_arity(); ++i) {
                subst_vars[i] = m.mk_fresh_const("s", arith_util(m).mk_int());
            }
            to_rank = apply_subst(to_rank, subst_vars);
            subst_vars.reverse();
            expr_ref bound(m), decrease(m);
            if (well_founded(subst_vars, to_rank, bound, decrease)) {
                STRACE("predabst", tout << "=====================================\n";);
                STRACE("predabst", tout << "Formula is well-founded!\n";);
                STRACE("predabst", tout << "=====================================\n";);
                STRACE("predabst", tout << "bound: predabst " << mk_pp(bound, m) << "\n";);
                STRACE("predabst", tout << "decrease: in predabst " << mk_pp(decrease, m) << "\n";);
            }
            else {
                STRACE("predabst", tout << "=====================================\n";);
                STRACE("predabst", tout << "Formula is not well-founded!\n";);
                STRACE("predabst", tout << "=====================================\n";);
                throw acr_error(r_id, not_wf);
            }
        }

        unsigned add_node(func_decl* sym, cube_t const& cube, unsigned r_id, node_vector const& nodes = node_vector()) {
            unsigned added_id = m_node2info.size();
            func_decl2node_set::obj_map_entry * sym_nodes_entry = m_func_decl2max_reach_node_set.find_core(sym);
            // first fixpoint check combined with maximality maintainance
            if (sym_nodes_entry) {
                // nodes exist at this sym
                node_set& sym_nodes = sym_nodes_entry->get_data().m_value;
                node_vector old_lt_nodes;
                for (node_set::iterator it = sym_nodes.begin(), end = sym_nodes.end(); it != end; ++it) {
                    cube_t& old_cube = m_node2info[*it].m_cube;
                    // if cube implies existing cube then nothing to add
                    if (cube_leq(cube, old_cube)) {
                        STRACE("predabst", tout << "New node is subsumed by node " << *it << "\n";);
                        CASSERT("predabst", old_lt_nodes.size() == 0);
                        return NON_NODE;
                    }
                    // stronger old cubes will not be considered maximal
                    if (cube_leq(old_cube, cube)) {
                        STRACE("predabst", tout << "New node subsumes node " << *it << "\n";);
                        old_lt_nodes.push_back(*it);
                    }
                }
                // (no???) fixpoint reached since didn't return
                // remove subsumed maximal nodes
                for (node_vector::iterator it = old_lt_nodes.begin(), end = old_lt_nodes.end(); it != end; ++it) {
                    sym_nodes.remove(*it);
                    m_node_worklist.remove(*it); // removing non-existent element is ok
                }
                sym_nodes.insert(added_id);
            }
            else {
                m_func_decl2max_reach_node_set.insert_if_not_there2(sym, node_set())->get_data().m_value.insert(added_id);
            }
            // no fixpoint reached hence create new node
            m_node_worklist.insert(added_id);
            m_node2info.push_back(node_info(sym, cube, r_id, nodes));
            STRACE("predabst", tout << "Added "; print_node(tout, added_id););
            return added_id;
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

        bool refine_unreachable(core_tree_info const& core_info, rule_set const& rules) {
            refine_cand_info allrels_info(m);
            core_clauses clauses = mk_core_clauses(core_info, rules, allrels_info);
            vector<refine_pred_info> interpolants = solve_clauses(clauses, m);
            return refine_preds(allrels_info, interpolants);
        }

        bool refine_t_reach(unsigned node_id, rule_set const& rules) {
            expr_ref cs = mk_leaf(expr_ref_vector(m), node_id, rules);
            expr_ref imp(m.mk_not(cs), m);
            return m_template.constrain_template(imp);
        }

        bool refine_t_wf(unsigned node_id, rule_set const& rules) {
            rule* r = rules.get_rule(m_node2info[node_id].m_parent_rule);
            expr_ref_vector head_args = get_fresh_head_args(r, "s");
            core_clauses2 clauses;
            expr_ref to_wf(m.mk_true(), m);
            refine_cand_info to_refine_cand_info(m);
            mk_core_tree_WF(r->get_decl(), head_args, node_id, rules, clauses, to_wf, to_refine_cand_info);
            to_refine_cand_info.insert(r->get_decl(), head_args);

            expr_ref bound_sol(m);
            expr_ref decrease_sol(m);
            vector<refine_pred_info> interpolants;

            if (well_founded(head_args, to_wf, bound_sol, decrease_sol)) {
                interpolants.push_back(refine_pred_info(bound_sol, get_all_pred_vars(bound_sol)));
                interpolants.push_back(refine_pred_info(decrease_sol, get_all_pred_vars(decrease_sol)));
                for (unsigned i = 0; i < interpolants.size(); i++) {
                    STRACE("predabst", interpolants.get(i).display(tout););
                }
                return refine_preds(to_refine_cand_info, interpolants);
            }
            expr_ref cs = mk_leaf(head_args, node_id, rules);
            expr_ref_vector cs_vars(get_all_pred_vars(cs));

            app_ref_vector q_vars(m);
            for (unsigned j = 0; j < cs_vars.size(); j++) {
                if (!head_args.contains(cs_vars.get(j))) {
                    q_vars.push_back(to_app(cs_vars.get(j)));
                }
            }

            qe_lite ql1(m);
            ql1(q_vars, cs);
            expr_ref bound_cs(m);
            expr_ref decrease_cs(m);
            well_founded_cs(head_args, bound_cs, decrease_cs);
            expr_ref to_solve(m.mk_or(m.mk_not(cs), m.mk_and(bound_cs, decrease_cs)), m);
            return m_template.constrain_template(to_solve);
        }

        bool refine_preds(refine_cand_info const& allrels_info, vector<refine_pred_info> const& interpolants) {
            STRACE("predabst", tout << "Found " << interpolants.size() << " interpolants\n";);
            unsigned new_preds_added = 0;
            if (interpolants.size() > 0) {
                for (unsigned i = 0; i < allrels_info.get_info().size(); i++) {
                    for (unsigned j = 0; j < m_func_decls.size(); j++) {
                        func_decl *fd = to_func_decl(m_func_decls.get(j));
                        if (allrels_info.get_info().get(i).first == fd) {
                            vars_preds vp;
                            bool found = m_func_decl2vars_preds.find(fd, vp);
                            CASSERT("predabst", found);
                            expr_ref_vector vars(m, fd->get_arity(), vp.first);
                            vector<expr_ref_vector> rel_info = allrels_info.get_info().get(i).second;
                            for (unsigned k = 0; k < rel_info.size(); k++) {
                                new_preds_added += get_interpolant_pred(rel_info.get(k), vars, interpolants, *vp.second);
                            }
                            break;
                        }
                    }
                }
            }
            STRACE("predabst", tout << "Found " << new_preds_added << " new predicates\n";);
            return (new_preds_added > 0);
        }

        static bool is_args_pred(expr_ref_vector const& args, expr_ref_vector const& pred_vars) {
            for (unsigned j = 0; j < pred_vars.size(); j++) {
                if (!args.contains(pred_vars.get(j))) {
                    return false;
                }
            }
            return true;
        }

        unsigned get_interpolant_pred(expr_ref_vector const& args, expr_ref_vector const& vars, vector<refine_pred_info> const& interpolants, expr_ref_vector& in_preds) {
            unsigned new_preds_added = 0;
            for (unsigned i = 0; i < interpolants.size(); i++) {
                if (is_args_pred(args, interpolants.get(i).pred_vars)) {
                    expr_ref const& in_pred = interpolants.get(i).pred;
                    expr_ref in_pred2(replace_pred(args, vars, in_pred), m);
                    if (!in_preds.contains(in_pred2)) {
                        in_preds.push_back(in_pred2);
                        ++new_preds_added;
                    }
                }
            }
            return new_preds_added;
        }

        bool mk_core_tree(rule_set const& rules, unsigned node_id, core_tree_info &core_info) {
            try {
                smt_params new_param;
                smt::kernel solver(m, new_param);
                vector<name2symbol> names;
                core_tree core;
                mk_core_tree_internal(0, expr_ref_vector(m), node_id, 0, rules, solver, 0, names, core);
                return false;
            }
            catch (core_tree_info const& core_info2) {
                core_info = core_info2;
                return true;
            }
        }

        // Note: root_id is always passed as zero, and never modified or used (except to give to the exception...)
        // Note: all args but the first three should arguably be class members.
        void mk_core_tree_internal(unsigned hname, expr_ref_vector const& hargs, unsigned n_id, unsigned root_id, rule_set const& rules, smt::kernel& solver,
                                   unsigned count, vector<name2symbol>& names_map, core_tree& core) {
            STRACE("predabst", tout << "mk_core_tree_internal: node " << n_id << "; " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << ")\n";);
            node_info const& node = m_node2info[n_id];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst = get_subst_vect(r, hargs);
            unsigned univ_iter = hargs.size() + 1; // XXX why not zero?
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            for (unsigned i = usz; i < tsz; i++) {
                expr_ref as = apply_subst(r->get_tail(i), rule_subst);
                solver.assert_expr(as);
                if (solver.check() == l_false) {
                    throw core_tree_info(root_id, hname, n_id, univ_iter, names_map, core);
                }
                univ_iter++;
            }
            vector<std::pair<std::pair<unsigned, expr_ref_vector>, unsigned> > todo;
            vector<unsigned> names;
            for (unsigned i = 0; i < usz; i++) { // Each iteration corresponds to an in-arrow to this node.
                expr_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                app *a = to_app(qs_i);
                expr_ref_vector qargs(m, a->get_decl()->get_arity(), a->get_args());
                expr_ref orig_temp_body(m);
                if (m_template.get_orig_template(a, orig_temp_body)) {
                    STRACE("predabst", tout << "mk_core_tree_internal: found template for query symbol " << a->get_decl()->get_name() << "\n";);
                    qargs.append(m_template.get_params());
                    qargs.reverse();
                    orig_temp_body = apply_subst(orig_temp_body, qargs);
                    expr_ref_vector inst_body_terms = get_conj_terms(orig_temp_body);
                    for (unsigned j = 0; j < inst_body_terms.size(); j++) {
                        solver.assert_expr(inst_body_terms.get(j));
                        if (solver.check() == l_false) {
                            throw core_tree_info(root_id, hname, n_id, univ_iter, names_map, core);
                        }
                        univ_iter++;
                    }
                }
                else {
                    STRACE("predabst", tout << "mk_core_tree_internal: no template for query symbol " << a->get_decl()->get_name() << "\n";);
                    count++;
                    names.push_back(count);
                    names_map.insert(std::make_pair(count, a->get_decl())); // maps name id to query symbol decl
                    todo.push_back(std::make_pair(std::make_pair(count, qargs), node.m_parent_nodes.get(i))); // (name id, tail predicate args, parent node id); these form the first three args to mk_core_tree_internal
                }
            }
            core.insert(std::make_pair(hname, std::make_pair(std::make_pair(n_id, node.m_parent_nodes), names)));
            for (unsigned i = 0; i < todo.size(); i++) {
                mk_core_tree_internal(todo.get(i).first.first, todo.get(i).first.second, todo.get(i).second, root_id, rules, solver, count, names_map, core);
            }
        }

        void mk_core_tree_WF(func_decl* hname, expr_ref_vector hargs, unsigned n_id, rule_set const& rules, core_clauses2& clauses, expr_ref& to_wf, refine_cand_info& refine_cand_info_set) {
            STRACE("predabst", tout << "mk_core_tree_WF: node " << n_id << "; " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << ")\n";);
            node_info const& node = m_node2info[n_id];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst = get_subst_vect(r, hargs);
            unsigned usz = r->get_uninterpreted_tail_size(), tsz = r->get_tail_size();
            expr_ref cs = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
            vector<std::pair<func_decl*, std::pair<expr_ref_vector, unsigned> > > todo;
            expr_ref_vector cl_bs(m);
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                app *a = to_app(qs_i);
                expr_ref_vector qs_i_vars(m, a->get_decl()->get_arity(), a->get_args());
                expr_ref inst_body(m), temp_body(m);
                for (unsigned j = 0; j < a->get_num_args(); j++) {
                    refine_cand_info_set.insert(a->get_decl(), qs_i_vars);
                }
                if (m_template.get_orig_template(a, temp_body)) {
                    expr_ref_vector temp_subst(m);
                    for (unsigned i = 0; i < m_template.get_params().size(); i++) {
                        temp_subst.push_back(rule_subst.get(i));
                    }
                    temp_subst.append(rule_subst);
                    temp_body = apply_subst(temp_body, temp_subst);
                    m_template.get_modref().get()->eval(temp_body, inst_body);
                    cs = mk_conj(cs, inst_body);
                }
                else {
                    todo.push_back(std::make_pair(a->get_decl(), std::make_pair(qs_i_vars, node.m_parent_nodes.get(i))));
                    cl_bs.push_back(qs_i);
                }
            }
            clauses.insert(std::make_pair(hname, std::make_pair(hargs, std::make_pair(cs, cl_bs))));
            to_wf = mk_conj(to_wf, cs);
            for (unsigned i = 0; i < todo.size(); i++) {
                mk_core_tree_WF(todo.get(i).first, todo.get(i).second.first, todo.get(i).second.second, rules, clauses, to_wf, refine_cand_info_set);
            }
        }

        core_clauses mk_core_clauses(core_tree_info const& core_info, rule_set const& rules, refine_cand_info &allrels_info) {
            expr_ref_vector last_vars(m);
            core_clauses clauses;
            mk_core_clauses_internal(core_info.m_root_id, expr_ref_vector(m), core_info.m_last_name, core_info.m_core, rules, last_vars, clauses, allrels_info);
            expr_ref_vector body = last_clause_body(last_vars, core_info.m_pos, core_info.m_last_node_tid, rules);
            expr_ref cs = mk_conj(body);
            STRACE("predabst", tout << "mk_core_clauses: adding final clause " << core_info.m_last_name << "("; print_expr_ref_vector(tout, last_vars); tout << "); " << mk_pp(cs, m) << "\n";);
            clauses.insert(std::make_pair(core_info.m_last_name, std::make_pair(last_vars, std::make_pair(cs, expr_ref_vector(m)))));
            return clauses;
        }

        // The last parameter builds up information that will ultimately be passed to refine_preds.
        void mk_core_clauses_internal(unsigned hname, expr_ref_vector hargs, unsigned last_name, core_tree const& core,
                             rule_set const& rules,
                             expr_ref_vector& last_vars, core_clauses& clauses, refine_cand_info& refine_cand_info_set) {
            STRACE("predabst", tout << "mk_core_clauses_internal: " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << "); " << last_name << "\n";);
            core_tree::const_iterator it = core.find(hname);
            node_info const& node = m_node2info[it->second.first.first];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst = get_subst_vect(r, hargs);
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref cs = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
            vector<std::pair<unsigned, expr_ref_vector> > todo;
            expr_ref_vector cl_bs(m);
            vector<unsigned> const& names = it->second.second;
            unsigned name_count = 0;
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                app *a = to_app(qs_i);
                expr_ref_vector qargs(m, a->get_decl()->get_arity(), a->get_args());
                expr_ref inst_body(m);
                expr_ref orig_temp_body(m);
                for (unsigned j = 0; j < a->get_num_args(); j++) {
                    STRACE("predabst", tout << "Recording " << a->get_decl()->get_name() << "("; print_expr_ref_vector(tout, qargs, false); tout << ")\n";);
                    refine_cand_info_set.insert(a->get_decl(), qargs);
                }
                if (m_template.get_orig_template(a, orig_temp_body)) {
                    STRACE("predabst", tout << "mk_core_clauses_internal: found template for query symbol " << a->get_decl()->get_name() << "\n";);
                    expr_ref_vector temp_subst(m_template.get_params());
                    temp_subst.append(rule_subst);
                    orig_temp_body = apply_subst(orig_temp_body, temp_subst);
                    m_template.get_modref().get()->eval(orig_temp_body, inst_body);
                    cs = mk_conj(cs, inst_body);
                }
                else {
                    STRACE("predabst", tout << "mk_core_clauses_internal: no template for query symbol " << a->get_decl()->get_name() << "\n";);
                    cl_bs.push_back(qs_i);
                    if (core.find(names.get(name_count)) != core.end()) {
                        todo.push_back(std::make_pair(names.get(name_count), qargs));
                    }
                    else if (names.get(i) == last_name) {
                        last_vars.append(qargs);
                    }
                    name_count++;
                }
            }
            if (hargs.size() > 0 || !m.is_true(cs)) {
                STRACE("predabst", tout << "mk_core_clauses_internal: adding clause " << hname << "("; print_expr_ref_vector(tout, hargs, false); tout << "); " << mk_pp(cs, m) << "; "; print_expr_ref_vector(tout, cl_bs););
                clauses.insert(std::make_pair(hname, std::make_pair(hargs, std::make_pair(cs, cl_bs))));
            }

            for (unsigned i = 0; i < todo.size(); i++) {
                mk_core_clauses_internal(todo.get(i).first, todo.get(i).second, last_name, core, rules, last_vars, clauses, refine_cand_info_set);
            }
        }

        expr_ref_vector last_clause_body(expr_ref_vector const& hvars, unsigned crit_pos, unsigned tid, rule_set const& rules) {
            node_info const& node = m_node2info[tid];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst = get_subst_vect(r, hvars);
            expr_ref_vector body(m);
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            unsigned curr_pos = hvars.size() + 1;
            for (unsigned i = usz; i < tsz; i++) {
                expr_ref as = apply_subst(r->get_tail(i), rule_subst);
                if (!m.is_true(as)) {
                    body.push_back(as);
                }
                if (curr_pos == crit_pos) {
                    return body;
                }
                curr_pos++;
            }
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                expr_ref inst_body(m);
                expr_ref_vector tmp(m);
                if (m_template.get_instance(to_app(qs_i), inst_body, tmp)) {
                    expr_ref_vector inst_body_terms = get_conj_terms(inst_body);
                    for (unsigned j = 0; j < inst_body_terms.size(); j++) {
                        body.push_back(inst_body_terms.get(j));
                        if (curr_pos == crit_pos) {
                            return body;
                        }
                        curr_pos++;
                    }
                }
            }
            body.reset(); // >>> is this necessary, or will it always be empty at this point?
            return body;
        }

        expr_ref mk_leaf(expr_ref_vector hargs, unsigned n_id, rule_set const& rules) {
            expr_ref cs(m.mk_true(), m);
            mk_leaf(hargs, n_id, rules, cs);
            return cs;
        }

        void mk_leaf(expr_ref_vector hargs, unsigned n_id, rule_set const& rules, expr_ref& cs) {
            node_info const& node = m_node2info[n_id];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst = get_subst_vect(r, hargs);
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref conj = apply_subst(mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz)), rule_subst);
            cs = mk_conj(cs, conj);
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i = apply_subst(r->get_tail(i), rule_subst);
                expr_ref_vector qs_i_vars(m, to_app(qs_i)->get_decl()->get_arity(), to_app(qs_i)->get_args());
                if (m_template.get_names().contains(r->get_decl(i))) {
                    cs = mk_conj(cs, qs_i);
                }
                else {
                    mk_leaf(qs_i_vars, node.m_parent_nodes.get(i), rules, cs);
                }
            }
        }

        // Returns a vector of fresh constants of the right type to be arguments to the head of rule r.
        expr_ref_vector get_fresh_head_args(rule const* r, char const* prefix) {
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            unsigned num_args = r->get_head()->get_num_args();
            expr_ref_vector head_args(m);
            head_args.reserve(num_args);
            for (unsigned i = 0; i < num_args; ++i) {
                head_args[i] = m.mk_fresh_const(prefix, free_sorts[i]); // XXX this is nonsense; free_sorts[i] is not the type of argument i!
            }
            return head_args;
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) covering all the variables used by r, which maps variables
        // 0..len(hvars)-1 to reversed(hvars), and maps n.. to fresh constants.
        // XXX reversed(hvars)?
        // XXX where does hvars come from, and is it really for a contiguous
        // range of variables?
        // XXX this is nonsense!!!
        expr_ref_vector get_subst_vect(rule const* r, expr_ref_vector const& hvars) {
            //CASSERT("predabst", hvars.size() == r->get_decl()->get_arity());
            // XXX This assert should be enabled, but it causes tests to fail...
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            CASSERT("predabst", free_sorts.size() >= hvars.size());
            unsigned fresh_subst_size = free_sorts.size() - hvars.size();
            expr_ref_vector rule_subst(m);
            rule_subst.reserve(fresh_subst_size);
            for (unsigned i = 0; i < fresh_subst_size; ++i) {
                rule_subst[i] = m.mk_fresh_const("s", free_sorts[i]);
            }
            rule_subst.append(hvars);
            rule_subst.reverse();
            return rule_subst;
        }

        expr_ref_vector get_subst_vect_free(rule const* r, char const* prefix) {
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            expr_ref_vector rule_subst(m);
            rule_subst.reserve(free_sorts.size());
            for (unsigned i = 0; i < free_sorts.size(); ++i) {
                app *c = m.mk_fresh_const(prefix, free_sorts[i]);
                STRACE("predabst", tout << "  substituting " << mk_pp(c, m) << " for var " << i << " of type " << mk_pp(free_sorts[i], m) << "\n";);
                rule_subst[i] = c;
            }
            return rule_subst;
        }

        void print_trace(std::ostream& out, unsigned n_id) {
            node_set todo_nodes;
            todo_nodes.insert(n_id);
            out << "Error trace:\n";
            while (!todo_nodes.empty()) {
                unsigned curr_id = *todo_nodes.begin();
                todo_nodes.remove(curr_id);
                node_info const& node = m_node2info[curr_id];
                out << "(" << curr_id << ", " << node.m_func_decl->get_name() << ", " << node.m_parent_rule << ", [";
                for (unsigned i = 0; i < node.m_parent_nodes.size(); i++) {
                    out << node.m_parent_nodes.get(i) << " ";
                }
                out << "])\n";
                for (unsigned i = 0; i < node.m_parent_nodes.size(); ++i) {
                    todo_nodes.insert(node.m_parent_nodes[i]);
                }
            }
        }

        void print_core_tree(std::ostream& out, core_tree const& core) {
            for (unsigned i = 0; i < core.size(); i++) {
                out << "core_hname: " << core.find(i)->first << ", core_id: " << core.find(i)->second.first.first << ", core_ids: [";
                for (unsigned j = 0; j < core.find(i)->second.first.second.size(); j++) {
                    out << " " << core.find(i)->second.first.second.get(j);
                }
                out << "], core_body_names: [";
                for (unsigned j = 0; j < core.find(i)->second.second.size(); j++) {
                    out << " " << core.find(i)->second.second.get(j);
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

        void print_predabst_state(std::ostream& out) const {
            out << "collected predicates:" << std::endl;
            for (func_decl2vars_preds::iterator it = m_func_decl2vars_preds.begin(),
                     end = m_func_decl2vars_preds.end(); it != end; ++it) {
                out << "preds " << it->m_key->get_name() << " "
                    << it->m_value.second->size() << " :";
                print_expr_ref_vector(out, *(it->m_value.second));
            }
            out << "instantiated predicates" << std::endl;
            for (unsigned r_id = 0; r_id < m_rule2info.size(); ++r_id) {
                out << "inst " << r_id << ": "
                    << mk_pp(m_rule2info[r_id].m_body, m) << std::endl;
                out << "  head: ";
                print_expr_ref_vector(out, m_rule2info[r_id].m_head_preds);
                vector<expr_ref_vector> const& body_preds_vector = m_rule2info[r_id].m_body_preds;
                for (unsigned i = 0; i < body_preds_vector.size(); ++i) {
                    out << "  body #" << i << ": ";
                    print_expr_ref_vector(out, body_preds_vector[i]);
                }
            }
            out << "rule dependency" << std::endl;
            for (func_decl2rule_set::iterator it = m_func_decl2rules.begin(),
                     end = m_func_decl2rules.end(); it != end; ++it) {
                out << it->m_key->get_name() << ": "
                    << it->m_value << std::endl;
            }
        }

        void print_node(std::ostream& out, unsigned n_id) const {
            node_info const& node = m_node2info[n_id];
            out << "node " << n_id << " (" << node.m_func_decl->get_name()
                << "): from (" << node.m_parent_nodes
                << ") via " << node.m_parent_rule
                << " giving [" << node.m_cube << "]"
                << std::endl;
        }

        void print_inference_state(std::ostream& out) const {
            for (unsigned i = 0; i < m_node2info.size(); ++i) {
                print_node(out, i);
            }
            for (func_decl2node_set::iterator
                it = m_func_decl2max_reach_node_set.begin(),
                end = m_func_decl2max_reach_node_set.end();
                it != end; ++it) {
                out << "max reached nodes " << it->m_key->get_name() << ": "
                    << it->m_value << std::endl;
            }
            out << "worklist " << m_node_worklist << std::endl;
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
