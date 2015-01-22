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

        struct rule_info {
            expr_ref                m_body;
            vector<expr_ref_vector> m_preds;
            rule_info(expr_ref& body) : m_body(body) {}
        };

        class scoped_push {
            smt::kernel& s;
        public:
            scoped_push(smt::kernel& s) : s(s) { s.push(); }
            ~scoped_push() { s.pop(1); }
        };

        context&               m_ctx;         // main context where (fixedpoint) constraints are stored.
        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        rule_manager&          rm;            // context with utilities for fixedpoint rules.
        smt_params             m_fparams;     // parameters specific to smt solving
        smt::kernel            m_solver;      // basic SMT solver class
        var_subst              m_var_subst;   // substitution object. It gets updated and reset.
        volatile bool          m_cancel;      // Boolean flag to track external cancelation.
        stats                  m_stats;       // statistics information specific to the CLP module.

        typedef obj_map<func_decl, std::pair<expr* const*, expr_ref_vector*> > func_decl2vars_preds;
        func_decl2vars_preds m_func_decl2vars_preds;

        vector<rule_info> m_rule2info;

        typedef obj_map<func_decl, uint_set> func_decl2uints;
        func_decl2uints m_func_decl_body2rules;

        expr_ref_vector m_empty_preds;
        ast_ref_vector  m_ast_trail;

        typedef vector<bool> cube_t;
        typedef vector<unsigned> node_vector;
        struct node_info {
            func_decl*  m_func_decl;
            cube_t      m_cube;
            unsigned    m_parent_rule;
            node_vector m_parent_nodes;
            node_info() {}
            node_info(func_decl* f, cube_t& c, unsigned r, node_vector n) :
                m_func_decl(f),
                m_cube(c),
                m_parent_rule(r),
                m_parent_nodes(n)
                {}
        };
        typedef uint_set node_set;
        typedef obj_map<func_decl, node_set> func_decl2node_set;

        vector<node_info>  m_node2info;
        func_decl2node_set m_func_decl2max_reach_node_set;
        node_set           m_node_worklist;
        rel_template_suit  m_template;

    public:
        imp(context& ctx):
            m_ctx(ctx),
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_solver(m, m_fparams),
            m_var_subst(m, false),
            m_cancel(false),
            m_empty_preds(m),
            m_ast_trail(m),
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
            m_ctx.ensure_opened();
            rule_set& rules = m_ctx.get_rules();
            rm.mk_query(query, rules);
            ptr_vector<rule> to_delete;
            // collect predicates and delete corresponding rules
            for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                collect_predicates(rules, i, to_delete);
            }
            for (unsigned i = 0; !m_cancel && i < to_delete.size(); ++i) {
                rules.del_rule(to_delete[i]);
            }
            // collect templates and extra constraints on templates
            for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                collect_templates_extra(rules, i);
            }
            for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                collect_templates(rules, i);
            }
            m_template.init_template_instantiate();
            return abstract_check_refine(rules, 0);
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
                    throw "predabst::get_model zero arity";
                }
                func_decl2vars_preds::obj_map_entry* e =
                    m_func_decl2vars_preds.find_core(it_decl->m_key);
                expr_ref_vector disj(m);
                if (e) {
                    expr_ref_vector const& preds = *e->get_data().get_value().second;
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
                        disj.push_back(m.mk_and(conj.size(), conj.c_ptr()));
                    }
                }
                else {
                    disj.push_back(m.mk_true());
                }
                func_interp* fi = alloc(func_interp, m, it_decl->m_key->get_arity());
                fi->set_else(m.mk_or(disj.size(), disj.c_ptr()));
                md->register_decl(it_decl->m_key, fi);
            }
            func_decl_set false_func_decls;
            // unreachable body predicates are false
            for (func_decl2uints::iterator it = m_func_decl_body2rules.begin(),
                     end = m_func_decl_body2rules.end(); it != end; ++it) {
                if (!m_func_decl2max_reach_node_set.contains(it->m_key)) {
                    false_func_decls.insert(it->m_key);
                }
            }
            // unreachable head predicates are false
            rule_set& rules = m_ctx.get_rules();
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

        static const unsigned NON_NODE = UINT_MAX;

        typedef enum { reach, wf } acr_error_kind;

        struct reached_query {
            unsigned m_node;
            acr_error_kind m_kind;
            reached_query(unsigned node, acr_error_kind kind) : m_node(node), m_kind(kind) {}
        };

        void collect_predicates(rule_set& rules, unsigned r_id, ptr_vector<rule>& to_delete) {
            rule* r = rules.get_rule(r_id);
            if (!is_pred_abst(r)) {
                return;
            }
            func_decl* head_decl = r->get_decl();
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            func_decl* suffix_decl = m.mk_func_decl(symbol(suffix), head_decl->get_arity(), head_decl->get_domain(), head_decl->get_range());
            m_ast_trail.push_back(suffix_decl);
            // add predicates to m_func_decl2vars_preds
            expr_ref_vector* preds = alloc(expr_ref_vector, m);
            preds->reserve(r->get_tail_size());
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                (*preds)[i] = r->get_tail(i);
            }
            m_func_decl2vars_preds.insert(suffix_decl, std::make_pair(r->get_head()->get_args(), preds));
            // rule is not used for inference
            to_delete.push_back(r);
        }

        bool is_pred_abst(rule *r) const {
            return (r->get_uninterpreted_tail_size() == 0) &&
                (r->get_decl()->get_name().str().substr(0, 8) == "__pred__");
        }

        void collect_templates_extra(rule_set& rules, unsigned r_id) {
            rule* r = rules.get_rule(r_id);
            func_decl* head_decl = r->get_decl();
            if (!is_template_extra(head_decl)) {
                return;
            }
            expr_ref_vector temp_params(m, head_decl->get_arity(), r->get_head()->get_args());
            expr_ref extras(r->get_tail(0), m);
            arith_util arith(m);
            expr_ref_vector extra_subst(m);
            extra_subst.reserve(temp_params.size());
            for (unsigned i = 0; i < extra_subst.size(); ++i) {
                extra_subst[i] = expr_ref(m.mk_fresh_const("b", arith.mk_int()), m);
            }
            m_var_subst(extras, extra_subst.size(), extra_subst.c_ptr(), extras);
            m_template.process_template_extra(extra_subst, extras);
            rules.del_rule(r);
        }

        bool is_template_extra(func_decl * pred) const {
            return pred->get_name().str().substr(0, 15) == "__temp__extra__";
        }

        void collect_templates(rule_set& rules, unsigned r_id) {
            rule* r = rules.get_rule(r_id);
            func_decl* head_decl = r->get_decl();
            if (!is_template(head_decl)) {
                return;
            }
            symbol suffix(head_decl->get_name().str().substr(8).c_str());
            unsigned new_arity = (head_decl->get_arity() - m_template.get_params_count());

            arith_util arith(m);
            func_decl* suffix_decl = m.mk_func_decl(suffix, new_arity, head_decl->get_domain(), head_decl->get_range());

            if (m_template.get_names().contains(suffix)) {
                STRACE("predabst", tout << "Multiple templates found for : " << suffix.str() << "\n";);
                throw suffix;
            }
            else {
                expr_ref_vector temp_subst(m);
                temp_subst.reserve(new_arity);
                for (unsigned i = 0; i < temp_subst.size(); ++i) {
                    temp_subst[i] = m.mk_fresh_const("v", arith.mk_int());
                }
                expr_ref_vector all_subst(temp_subst);
                all_subst.append(m_template.get_params());
                all_subst.reverse();
                app* suffix_app = m.mk_app(suffix_decl, r->get_head()->get_args());
                app* suffix_app2 = m.mk_app(suffix_decl, new_arity, temp_subst.c_ptr());
                expr_ref body1(m), body2(m);
                m_var_subst(r->get_tail(0), m_template.get_params().size(), m_template.get_params().c_ptr(), body1);
                m_var_subst(r->get_tail(0), all_subst.size(), all_subst.c_ptr(), body2);
                m_template.process_template_sk(rel_template(suffix_app, body1));
                m_template.process_template(suffix, rel_template(suffix_app2, body2), temp_subst);
            }
            rules.del_rule(r);
        }

        bool is_template(func_decl * pred) const {
            return pred->get_name().str().substr(0, 8) == "__temp__";
        }

        lbool abstract_check_refine(rule_set& rules, unsigned acr_count) {
            STRACE("predabst", tout << "=====================================+++++++++++++++++++\n";);
            STRACE("predabst", tout << "ACR step : " << acr_count << "\n";);
            STRACE("predabst", tout << "=====================================+++++++++++++++++++\n";);
            try {
                // for each rule: ground body and instantiate predicates for applications
                for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                    instantiate_rule(rules, i);
                }
                // initial abstract inference
                initialize_abs_templates(rules);
                for (unsigned i = 0; !m_cancel && i < rules.get_num_rules(); ++i) {
                    initialize_abs(rules, i);
                }
                // process worklist
                while (!m_cancel && !m_node_worklist.empty()) {
                    TRACE("dl", print_inference_state(tout););
                    unsigned current_id = *m_node_worklist.begin();
                    m_node_worklist.remove(current_id);
                    inference_step(rules, current_id);
                }
            }
            catch (reached_query& exc) {
                mk_trace(exc.m_node);
                if (refine_t(rules, exc)) {
                    //clean up before next ACR
                    m_rule2info.reset();
                    m_node_worklist.reset();
                    m_node2info.reset();
                    m_func_decl2max_reach_node_set.reset();
                    m_func_decl_body2rules.reset();
                    acr_count++;
                    return abstract_check_refine(rules, acr_count);
                }
                STRACE("predabst", tout << "UNSAT***!\n";);
                return l_true;
            }
            if (m_cancel) {
                return l_undef;
            }
            STRACE("predabst", tout << "SAT***!\n";);
            return l_false;
        }

        void instantiate_rule(rule_set const& rules, unsigned r_id) {
            rule* r = rules.get_rule(r_id);
            // prepare grounding substitution
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            expr_ref_vector rule_subst(m);
            rule_subst.reserve(free_sorts.size());
            for (unsigned i = 0; i < rule_subst.size(); ++i) {
                rule_subst[i] = m.mk_fresh_const("c", free_sorts[i]);
            }
            // conjoin constraints in rule body
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref conj(m.mk_and(tsz - usz, r->get_expr_tail() + usz), m);
            // apply substitution
            m_var_subst(conj, rule_subst.size(), rule_subst.c_ptr(), conj);
            // store ground body and instantiations
            rule_info info(conj);
            vector<expr_ref_vector>& preds = info.m_preds;
            // store instantiation for body applications
            for (unsigned i = 0; i < usz; ++i) {
                preds.push_back(expr_ref_vector(m));
                app_inst_preds(r->get_tail(i), rule_subst, preds[i]);
            }
            // store instantiation for non-query head
            if (!rules.is_output_predicate(r->get_decl())) {
                expr_ref_vector heads(m);
                app_inst_preds(r->get_head(), rule_subst, heads);
                for (unsigned i = 0; i < heads.size(); ++i) {
                    heads[i] = m.mk_not(heads[i].get());
                }
                preds.push_back(heads);
            }
            m_rule2info.push_back(info);
            // map body func_decls to rule
            for (unsigned i = 0; i < usz; ++i) {
                m_func_decl_body2rules.insert_if_not_there2(r->get_decl(i), uint_set())->get_data().m_value.insert(r_id);
            }
        }

        // ground arguments of app using subst, and then instantiate each predicate
        // by replacing its free variables with grounded arguments of app
        void app_inst_preds(app* appl, expr_ref_vector const& subst, expr_ref_vector& inst_preds) {
            func_decl2vars_preds::obj_map_entry* e = m_func_decl2vars_preds.find_core(appl->get_decl());
            if (!e) {
                expr_ref_vector* preds = alloc(expr_ref_vector, m);
                m_func_decl2vars_preds.insert(appl->get_decl(), std::make_pair(appl->get_args(), preds));
                m_ast_trail.push_back(appl->get_decl());
                return;
            }
            expr* const* vars = e->get_data().get_value().first;
            expr_ref_vector& preds = *e->get_data().get_value().second;
            // ground appl arguments
            expr_ref subst_tmp(m);
            m_var_subst(appl, subst.size(), subst.c_ptr(), subst_tmp);
            // instantiation maps preds variables to head arguments
            expr_ref_vector inst(m);
            inst.reserve(appl->get_num_args());
            app* gappl = to_app(subst_tmp);
            for (unsigned i = 0; i < appl->get_num_args(); ++i) {
                unsigned idx = to_var(vars[i])->get_idx();
                if (idx >= inst.size()) {
                    inst.resize(idx + 1);
                }
                inst[idx] = gappl->get_arg(i);
            }
            // preds instantiates to inst_preds
            inst_preds.reserve(preds.size());
            for (unsigned i = 0; i < preds.size(); ++i) {
                m_var_subst(preds[i].get(), inst.size(), inst.c_ptr(), subst_tmp);
                inst_preds[i] = subst_tmp;
            }
        }

        void initialize_abs_templates(rule_set& rules) {
            unsigned inst_r_id = rules.get_num_rules();
            for (unsigned i = 0; i < m_template.get_template_instances().size(); i++) {
                cube_t cube;
                if (cart_temp_pred_abst_rule(m_template.get_template_instances().get(i), m_template.get_orig_templates().get(i), cube)) {
                    add_node(m_template.get_orig_templates().get(i).m_head->get_decl(), cube, inst_r_id, node_vector());
                    inst_r_id++;
                }
                else {
                    throw m_template.get_template_instances().get(i).m_head;
                }
            }
        }

        void initialize_abs(rule_set const& rules, unsigned r_id) {
            rule* r = rules.get_rule(r_id);
            cube_t cube;
            if (r->get_uninterpreted_tail_size() == 0 && cart_pred_abst_rule(r_id, cube)) {
                check_node_property(rules, add_node(r->get_decl(), cube, r_id));
            }
        }

        void inference_step(rule_set const& rules, unsigned current_id) {
            func_decl* current_func_decl = m_node2info[current_id].m_func_decl;
            func_decl2uints::obj_map_entry* e_current_rules = m_func_decl_body2rules.find_core(current_func_decl);
            if (!e_current_rules) {
                return;
            }
            //get all rules whose body contains the symbol with a new node
            uint_set& current_rules = e_current_rules->get_data().m_value;
            //iterate over each rule
            for (uint_set::iterator r_id = current_rules.begin(), r_id_end = current_rules.end(); r_id != r_id_end; ++r_id) {
                // positions of current_id among body func_decls
                uint_set current_poss;
                rule* r = rules.get_rule(*r_id);
                for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                    if (r->get_decl(i) == current_func_decl) current_poss.insert(i);
                }
                // create set of combinations of nodes to apply the rule
                vector<node_vector> nodes_set;
                nodes_set.push_back(node_vector());
                // current_id is put on each appropriate position
                for (uint_set::iterator current_pos = current_poss.begin(), current_pos_end = current_poss.end(); current_pos != current_pos_end; ++current_pos) {
                    node_set current_pos_singleton;
                    current_pos_singleton.insert(current_id);
                    // grow node combinations as cartesian product with nodes at pos
                    for (unsigned pos = 0; pos < r->get_uninterpreted_tail_size(); ++pos) {
                        node_set& pos_nodes = (*current_pos == pos) ? current_pos_singleton : m_func_decl2max_reach_node_set[r->get_decl(pos)];
                        unsigned orig_nodes_set_size = nodes_set.size();
                        // compute cartesian product
                        // first, store the product with first node in place
                        node_set::iterator pos_node = pos_nodes.begin();
                        for (unsigned nodes_set_offset = 0; nodes_set_offset < orig_nodes_set_size; ++nodes_set_offset) {
                            nodes_set[nodes_set_offset].push_back(*pos_node);
                        }
                        ++pos_node;
                        // then, product for rest nodes goes into additional vectors
                        for (node_set::iterator pos_node_end = pos_nodes.end(); pos_node != pos_node_end; ++pos_node) {
                            for (unsigned nodes_set_offset = 0; nodes_set_offset < orig_nodes_set_size; ++nodes_set_offset) {
                                nodes_set.push_back(nodes_set[nodes_set_offset]);
                                nodes_set.back().push_back(*pos_node);
                            }
                        }
                    }
                }
                // apply rule on each node combination
                for (vector<node_vector>::iterator nodes = nodes_set.begin(), nodes_end = nodes_set.end(); nodes != nodes_end; ++nodes) {
                    cube_t cube;
                    if (cart_pred_abst_rule(*r_id, cube, *nodes)) {
                        check_node_property(rules, add_node(r->get_decl(), cube, *r_id, *nodes));
                    }
                }
            }
        }

        bool cart_temp_pred_abst_rule(rel_template instance, rel_template orig_temp, cube_t& cube) {
            func_decl2vars_preds::obj_map_entry* e = m_func_decl2vars_preds.find_core(orig_temp.m_head->get_decl());
            if (!e) {
                return false;
            }
            arith_util arith(m);
            expr_ref_vector temp_subst2(m_template.get_temp_subst());
            temp_subst2.reverse();
            scoped_push _push1(m_solver);
            m_solver.assert_expr(instance.m_body);
            if (m_solver.check() == l_false) {
                return false;
            }
            expr_ref_vector& preds = *e->get_data().get_value().second;
            cube.resize(preds.size());
            for (unsigned i = 0; i < preds.size(); ++i) {
                expr_ref subst_pred(m);
                m_var_subst(preds[i].get(), temp_subst2.size(), temp_subst2.c_ptr(), subst_pred);
                scoped_push _push2(m_solver);
                m_solver.assert_expr(subst_pred);
                cube[i] = (m_solver.check() == l_true);
            }
            return true;
        }

        bool cart_pred_abst_rule(unsigned r_id, cube_t& cube, node_vector const& nodes = node_vector()) {
            // get instantiated predicates
            vector<expr_ref_vector> const& preds_vector = m_rule2info[r_id].m_preds;
            scoped_push _push1(m_solver);
            m_solver.assert_expr(m_rule2info[r_id].m_body);
            // load abstract states for nodes
            for (unsigned pos = 0; pos < nodes.size(); ++pos) {
                cube_t& pos_cube = m_node2info[nodes[pos]].m_cube;
                for (unsigned i = 0; i < preds_vector[pos].size(); ++i) {
                    if (pos_cube[i]) {
                        m_solver.assert_expr(preds_vector[pos][i]);
                    }
                }

            }
            if (m_solver.check() == l_false) {
                // unsat body
                return false;
            }
            // collect abstract cube
            expr_ref_vector const& head_preds = preds_vector.back();
            cube.resize(head_preds.size());
            for (unsigned i = 0; i < head_preds.size(); ++i) {
                scoped_push _push2(m_solver);
                m_solver.assert_expr(head_preds[i]);
                cube[i] = (m_solver.check() == l_false);
            }
            return true;
        }

        void check_node_property(rule_set const& rules, unsigned id) {
            if (id != NON_NODE && rules.is_output_predicate(m_node2info[id].m_func_decl)) {
                throw reached_query(id, reach);
            }
            if (id != NON_NODE && is_wf_predicate(m_node2info[id].m_func_decl)) {
                check_well_founded(id);
            }
        }

        bool is_wf_predicate(func_decl * pred) const {
            return pred->get_name().str().substr(0, 6) == "__wf__";
        }

        void check_well_founded(unsigned r_id) {
            func_decl * pred = m_node2info[r_id].m_func_decl;
            cube_t cube = m_node2info[r_id].m_cube;
            func_decl2vars_preds::obj_map_entry* e = m_func_decl2vars_preds.find_core(pred);
            if (!e) {
                return;
            }
            expr* const* vars = e->get_data().get_value().first;
            expr_ref_vector preds_set = *(e->get_data().get_value().second);
            expr_ref to_rank(m.mk_true(), m);
            for (unsigned i = 0; i < cube.size(); i++) {
                STRACE("predabst", tout << "check_well_founded: considered cube " << mk_pp(preds_set[i].get(), m) << "\n";);
                if (cube[i]) {
                    mk_conj(to_rank, expr_ref(preds_set[i].get(), m), to_rank);
                    STRACE("predabst", tout << "check_well_founded: used cube " << mk_pp(preds_set[i].get(), m) << "\n";);
                }
            }
            expr_ref_vector subst_vars(m);
            arith_util arith(m);
            subst_vars.reserve(pred->get_arity());
            for (unsigned i = 0; i < pred->get_arity(); ++i) {
                subst_vars[i] = m.mk_fresh_const("s", arith.mk_int());
            }
            m_var_subst(to_rank, subst_vars.size(), subst_vars.c_ptr(), to_rank);
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
                throw reached_query(r_id, wf);
            }
        }

        unsigned add_node(func_decl* sym, cube_t& cube, unsigned r_id, node_vector const& nodes = node_vector()) {
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
                        return NON_NODE;
                    }
                    // stronger old cubes will not be considered maximal
                    if (cube_leq(old_cube, cube)) {
                        old_lt_nodes.push_back(*it);
                    }
                }
                // fixpoint reached since didn't return
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
            return added_id;
        }

        // return whether c1 implies c2
        bool cube_leq(cube_t const& c1, cube_t const& c2) const {
            unsigned size = c1.size();
            for (unsigned i = 0; i < size; ++i) {
                if (c2[i] && !c1[i]) {
                    return false;
                }
            }
            return true;
        }

        bool refine_t(rule_set& rules, reached_query reached_error) {
            unsigned node_id = reached_error.m_node;
            try {
                if (reached_error.m_kind == reach) {
                    return refine_t_reach(node_id, rules);
                }
                else {
                    return refine_t_wf(node_id, rules);
                }
            }
            catch (core_to_throw& from_throw) {
                return refine_unreachable(from_throw, node_id, rules);
            }
        }

        bool refine_t_reach(unsigned node_id, rule_set& rules) {
            node_info const& node = m_node2info[node_id];
            smt_params new_param;
            smt::kernel solver(m, new_param);
            vector<name2symbol> names;
            core_tree core;
            mk_core_tree(0, expr_ref_vector(m), node_id, 0, rules, solver, 0, names, core);
            expr_ref cs(m.mk_true(), m);
            mk_leaf(expr_ref_vector(m), node_id, rules, cs);
            expr_ref imp(m.mk_not(cs), m);
            if (m_template.constrain_template(imp)) {
                STRACE("predabst", tout << "reach***: template refinement successful!\n";);
                return true;
            }
            STRACE("predabst", tout << "reach***: template refinement NOT possible\n";);
            return false;
        }

        bool refine_t_wf(unsigned node_id, rule_set& rules) {
            smt_params new_param;
            smt::kernel solver(m, new_param);
            vector<name2symbol> names;
            core_tree core;
            mk_core_tree(0, expr_ref_vector(m), node_id, 0, rules, solver, 0, names, core);
            core_clauses2 clauses;
            refine_cand_info to_refine_cand_info(m);
            rule* r = rules.get_rule(m_node2info[node_id].m_parent_rule);
            unsigned fresh_subst_size = r->get_head()->get_num_args();
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            expr_ref_vector head_args(m);
            expr_ref to_wf(m.mk_true(), m);
            for (unsigned i = 0; i < fresh_subst_size; ++i) {
                head_args.push_back(m.mk_fresh_const("s", free_sorts.get(i)));
            }
            mk_core_tree_WF(r->get_head()->get_decl()->get_name(), head_args, node_id, rules, clauses, to_wf, to_refine_cand_info);
            to_refine_cand_info.insert(r->get_head()->get_decl()->get_name(), head_args);

            expr_ref bound_sol(m), decrease_sol(m);
            vector<refine_pred_info> interpolants;

            if (well_founded(head_args, to_wf, bound_sol, decrease_sol)) {
                interpolants.push_back(refine_pred_info(bound_sol, get_all_pred_vars(bound_sol)));
                interpolants.push_back(refine_pred_info(decrease_sol, get_all_pred_vars(decrease_sol)));
                for (unsigned i = 0; i < interpolants.size(); i++) {
                    STRACE("predabst", interpolants.get(i).display(tout););
                }
                if (refine_preds(to_refine_cand_info, interpolants)) {
                    return true;
                }
                STRACE("predabst", tout << "no new preds!\n";);
                return false;
            }
            expr_ref bound_cs(m), decrease_cs(m), cs(m.mk_true(), m);
            mk_leaf(head_args, node_id, rules, cs);

            expr_ref_vector cs_vars(get_all_pred_vars(cs));

            app_ref_vector q_vars(m);
            for (unsigned j = 0; j < cs_vars.size(); j++) {
                if (!head_args.contains(cs_vars.get(j))) {
                    q_vars.push_back(to_app(cs_vars.get(j)));
                }
            }

            qe_lite ql1(m);
            ql1(q_vars, cs);
            well_founded_cs(head_args, bound_cs, decrease_cs);
            expr_ref to_solve(m.mk_or(m.mk_not(cs), m.mk_and(bound_cs, decrease_cs)), m);
            if (m_template.constrain_template(to_solve)) {
                STRACE("predabst", tout << "wf***: template refinement successful!\n";);
                return true;
            }
            STRACE("predabst", tout << "wf***: template refinement NOT possible\n";);
            return false;
        }

        bool refine_unreachable(core_to_throw& from_throw, unsigned node_id, rule_set& rules) {
            core_clauses clauses;
            refine_cand_info allrels_info(m);
            expr_ref_vector last_vars(m);
            mk_core_clauses(from_throw.root_id, expr_ref_vector(m), from_throw.last_name, from_throw.core, rules, last_vars, clauses, allrels_info);
            expr_ref_vector body(m);
            try {
                last_clause_body(last_vars, from_throw.pos, from_throw.last_node_tid, from_throw.last_node_ids, rules);
            }
            catch (expr_ref_vector& th_body) {
                body.append(th_body);
            }
            expr_ref cs(m);
            mk_conj(body, cs);

            clauses.insert(std::make_pair(from_throw.last_name, std::make_pair(last_vars, std::make_pair(cs, expr_ref_vector(m)))));
            vector<refine_pred_info> interpolants;
            if (solve_clauses2(clauses, m, interpolants)) {
                if (refine_preds(allrels_info, interpolants)) {
                    return true;
                }
                STRACE("predabst", tout << "no new preds!\n";);
                return false;
            }
            return false;
        }

        bool refine_preds(refine_cand_info allrels_info, vector<refine_pred_info> interpolants) {
            bool new_preds_added = false;
            for (unsigned i = 0; i < allrels_info.get_info().size(); i++) {
                for (unsigned j = 0; j < m_ast_trail.size(); j++) {
                    if (allrels_info.get_info().get(i).first == to_func_decl(m_ast_trail.get(j))->get_name()) {
                        func_decl2vars_preds::obj_map_entry* e = m_func_decl2vars_preds.find_core(to_func_decl(m_ast_trail.get(j)));
                        expr_ref_vector vars(m, to_func_decl(m_ast_trail.get(j))->get_arity(), e->get_data().get_value().first);
                        vector<expr_ref_vector> rel_info = allrels_info.get_info().get(i).second;
                        unsigned st_preds_size = (*e->get_data().get_value().second).size();
                        for (unsigned k1 = 0; k1 < rel_info.size(); k1++) {
                            get_interpolant_pred(rel_info.get(k1), vars, interpolants, *e->get_data().get_value().second);
                        }
                        unsigned end_preds_size = (*e->get_data().get_value().second).size();
                        if (end_preds_size > st_preds_size) {
                            new_preds_added = true;
                        }
                        break;
                    }
                }
            }
            return new_preds_added;
        }

        void mk_core_tree(unsigned hname, expr_ref_vector hargs, unsigned n_id, unsigned root_id, rule_set rules, smt::kernel& solver,
            unsigned count, vector<name2symbol>& names_map, core_tree& core) {
            node_info const& node = m_node2info[n_id];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst(m);
            get_subst_vect(r, hargs, rule_subst);
            unsigned univ_iter = hargs.size() + 1, usz = r->get_uninterpreted_tail_size(), tsz = r->get_tail_size();
            for (unsigned i = usz; i < tsz; i++) {
                expr_ref as(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), as);
                solver.assert_expr(as);
                if (solver.check() == l_false) {
                    throw core_to_throw(root_id, hname, n_id, node.m_parent_nodes, univ_iter, names_map, core);
                }
                univ_iter++;
            }
            vector<std::pair<std::pair<unsigned, expr_ref_vector>, unsigned> > todo;
            vector<unsigned> names;
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), qs_i);
                expr_ref_vector qargs(m, to_app(qs_i)->get_decl()->get_arity(), to_app(qs_i)->get_args());
                expr_ref orig_temp_body(m);
                if (m_template.get_orig_template(to_app(qs_i), orig_temp_body)) {
                    qargs.append(m_template.get_params());
                    qargs.reverse();
                    m_var_subst(orig_temp_body, qargs.size(), qargs.c_ptr(), orig_temp_body);
                    expr_ref_vector inst_body_terms(m);
                    get_conj_terms(orig_temp_body, inst_body_terms);
                    for (unsigned j = 0; j < inst_body_terms.size(); j++) {
                        solver.assert_expr(inst_body_terms.get(j));
                        if (solver.check() == l_false) {
                            throw core_to_throw(root_id, hname, n_id, node.m_parent_nodes, univ_iter, names_map, core);
                        }
                        univ_iter++;
                    }
                }
                else {
                    count++;
                    names.push_back(count);
                    names_map.insert(std::make_pair(count, to_app(qs_i)->get_decl()->get_name()));
                    todo.insert(std::make_pair(std::make_pair(count, qargs), node.m_parent_nodes.get(i)));
                }
            }
            core.insert(std::make_pair(hname, std::make_pair(std::make_pair(n_id, node.m_parent_nodes), names)));
            for (unsigned i = 0; i < todo.size(); i++) {
                mk_core_tree(todo.get(i).first.first, todo.get(i).first.second, todo.get(i).second, root_id, rules, solver, count, names_map, core);
            }
        }

        void mk_core_tree_WF(symbol hname, expr_ref_vector hargs, unsigned n_id, rule_set rules, core_clauses2& clauses, expr_ref& to_wf, refine_cand_info& refine_cand_info_set) {
            node_info const& node = m_node2info[n_id];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst(m);
            get_subst_vect(r, hargs, rule_subst);
            expr_ref cs(m.mk_true(), m);
            unsigned usz = r->get_uninterpreted_tail_size(), tsz = r->get_tail_size();
            mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz), cs);
            m_var_subst(cs, rule_subst.size(), rule_subst.c_ptr(), cs);
            vector<std::pair<symbol, std::pair<expr_ref_vector, unsigned> > > todo;
            expr_ref_vector cl_bs(m);
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), qs_i);
                expr_ref_vector qs_i_vars(m, to_app(qs_i)->get_decl()->get_arity(), to_app(qs_i)->get_args());
                expr_ref inst_body(m), temp_body(m);
                for (unsigned j = 0; j < to_app(qs_i)->get_num_args(); j++) {
                    refine_cand_info_set.insert(to_app(qs_i)->get_decl()->get_name(), qs_i_vars);
                }
                if (m_template.get_orig_template(to_app(qs_i), temp_body)) {
                    expr_ref_vector temp_subst(m);
                    for (unsigned i = 0; i < m_template.get_params().size(); i++) {
                        temp_subst.push_back(rule_subst.get(i));
                    }
                    temp_subst.append(rule_subst);
                    m_var_subst(temp_body, temp_subst.size(), temp_subst.c_ptr(), temp_body);
                    m_template.get_modref().get()->eval(temp_body, inst_body);
                    mk_conj(cs, inst_body, cs);
                }
                else {
                    todo.push_back(std::make_pair(to_app(qs_i)->get_decl()->get_name(), std::make_pair(qs_i_vars, node.m_parent_nodes.get(i))));
                    cl_bs.push_back(qs_i);
                }
            }
            clauses.insert(std::make_pair(hname, std::make_pair(hargs, std::make_pair(cs, cl_bs))));
            mk_conj(to_wf, cs, to_wf);
            for (unsigned i = 0; i < todo.size(); i++) {
                mk_core_tree_WF(todo.get(i).first, todo.get(i).second.first, todo.get(i).second.second, rules, clauses, to_wf, refine_cand_info_set);
            }
        }

        void mk_core_clauses(unsigned hname, expr_ref_vector hargs, unsigned last_name, core_tree core,
            rule_set rules, expr_ref_vector& last_vars, core_clauses& clauses, refine_cand_info& refine_cand_info_set) {
            vector<unsigned> names;
            core_tree::iterator it = core.find(hname);
            node_info const& node = m_node2info[it->second.first.first];
            names = it->second.second;
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst(m);
            get_subst_vect(r, hargs, rule_subst);
            expr_ref cs(m.mk_true(), m);
            unsigned usz = r->get_uninterpreted_tail_size(), tsz = r->get_tail_size();
            mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz), cs);
            m_var_subst(cs, rule_subst.size(), rule_subst.c_ptr(), cs);
            vector<std::pair<unsigned, expr_ref_vector> > todo;
            expr_ref_vector cl_bs(m);
            unsigned name_count = 0;
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), qs_i);
                expr_ref_vector qs_i_vars(m, to_app(qs_i)->get_decl()->get_arity(), to_app(qs_i)->get_args());
                expr_ref inst_body(m), temp_body(m);
                for (unsigned j = 0; j < to_app(qs_i)->get_num_args(); j++) {
                    refine_cand_info_set.insert(to_app(qs_i)->get_decl()->get_name(), qs_i_vars);
                }
                if (m_template.get_orig_template(to_app(qs_i), temp_body)) {
                    expr_ref_vector temp_subst(m_template.get_params());
                    temp_subst.append(rule_subst);
                    m_var_subst(temp_body, temp_subst.size(), temp_subst.c_ptr(), temp_body);
                    m_template.get_modref().get()->eval(temp_body, inst_body);
                    mk_conj(cs, inst_body, cs);
                }
                else {
                    core_tree::iterator end = core.end();
                    if (core.find(names.get(name_count)) != end) {
                        cl_bs.push_back(qs_i);
                        todo.push_back(std::make_pair(names.get(name_count), qs_i_vars));
                    }
                    else if (names.get(i) == last_name) {
                        last_vars.append(qs_i_vars);
                        cl_bs.push_back(qs_i);
                    }
                    name_count++;
                }
            }
            if (hargs.size() > 0 || !m.is_true(cs)) {
                clauses.insert(std::make_pair(hname, std::make_pair(hargs, std::make_pair(cs, cl_bs))));
            }

            for (unsigned i = 0; i < todo.size(); i++) {
                mk_core_clauses(todo.get(i).first, todo.get(i).second, last_name, core, rules, last_vars, clauses, refine_cand_info_set);
            }
        }

        void last_clause_body(expr_ref_vector hvars, unsigned crit_pos, unsigned tid, vector<unsigned> ids, rule_set rules) {
            node_info const& node = m_node2info[tid];
            rule* r = rules.get_rule(node.m_parent_rule);
            expr_ref_vector rule_subst(m), body(m);
            get_subst_vect(r, hvars, rule_subst);
            unsigned usz = r->get_uninterpreted_tail_size(), tsz = r->get_tail_size(), curr_pos = hvars.size() + 1;
            for (unsigned i = usz; i < tsz; i++) {
                expr_ref as(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), as);
                if (!m.is_true(as)) {
                    body.push_back(as);
                }
                if (curr_pos == crit_pos) {
                    throw body;
                }
                curr_pos++;
            }
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i(m), inst_body(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), qs_i);
                expr_ref_vector tmp = expr_ref_vector(m);
                if (m_template.get_instance(to_app(qs_i), inst_body, tmp)) {
                    expr_ref_vector inst_body_terms(m);
                    get_conj_terms(inst_body, inst_body_terms);
                    for (unsigned j = 0; j < inst_body_terms.size(); j++) {
                        body.push_back(inst_body_terms.get(j));
                        if (curr_pos == crit_pos) {
                            throw body;
                        }
                        curr_pos++;
                    }
                }
            }
        }

        void mk_leaf(expr_ref_vector hargs, unsigned n_id, rule_set rules, expr_ref& cs) {
            node_info const& node = m_node2info[n_id];
            rule* r = rules.get_rule(node.m_parent_rule);
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            expr_ref_vector rule_subst(m);
            unsigned fresh_subst_size = free_sorts.size() - hargs.size();
            rule_subst.reserve(fresh_subst_size);
            for (unsigned i = 0; i < fresh_subst_size; ++i) {
                rule_subst[i] = m.mk_fresh_const("s", free_sorts[i]);
            }
            rule_subst.append(hargs);
            rule_subst.reverse();
            expr_ref conj(m.mk_true(), m);
            unsigned usz = r->get_uninterpreted_tail_size(), tsz = r->get_tail_size();
            mk_conj(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz), conj);
            m_var_subst(conj, rule_subst.size(), rule_subst.c_ptr(), conj);
            mk_conj(cs, conj, cs);
            for (unsigned i = 0; i < usz; i++) {
                expr_ref qs_i(m);
                m_var_subst(r->get_tail(i), rule_subst.size(), rule_subst.c_ptr(), qs_i);
                expr_ref_vector qs_i_vars(m, to_app(qs_i)->get_decl()->get_arity(), to_app(qs_i)->get_args());
                if (m_template.get_names().contains(r->get_tail(i)->get_decl()->get_name())) {
                    mk_conj(cs, qs_i, cs);
                }
                else {
                    mk_leaf(qs_i_vars, node.m_parent_nodes.get(i), rules, cs);
                }
            }
        }

        void get_subst_vect(rule* r, expr_ref_vector hvars, expr_ref_vector& rule_subst) {
            ptr_vector<sort> free_sorts;
            r->get_vars(m, free_sorts);
            unsigned fresh_subst_size = free_sorts.size() - hvars.size();
            rule_subst.reserve(fresh_subst_size);
            for (unsigned i = 0; i < fresh_subst_size; ++i) {
                rule_subst[i] = m.mk_fresh_const("s", free_sorts[i]);
            }
            rule_subst.append(hvars);
            rule_subst.reverse();
        }

        void mk_trace(unsigned n_id) {
            node_set todo_nodes;
            todo_nodes.insert(n_id);
            STRACE("predabst", tout << "Error trace:\n";);
            while (!todo_nodes.empty()) {
                unsigned curr_id = *todo_nodes.begin();
                todo_nodes.remove(curr_id);
                node_info const& node = m_node2info[curr_id];
                STRACE("predabst", tout << "(" << curr_id << ", " << node.m_func_decl->get_name().str() << ", " << node.m_parent_rule << ", [";);
                for (unsigned i = 0; i < node.m_parent_nodes.size(); i++) {
                    STRACE("predabst", tout << node.m_parent_nodes.get(i) << " ";);
                }
                STRACE("predabst", tout << "])\n";);
                for (unsigned i = 0; i < node.m_parent_nodes.size(); ++i) {
                    todo_nodes.insert(node.m_parent_nodes[i]);
                }
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
                out << "preds " << mk_pp(it->m_key, m) << " "
                    << it->m_value.second->size() << " :";
                print_expr_ref_vector(out, *(it->m_value.second));
            }
            out << "instantiated predicates" << std::endl;
            for (unsigned r_id = 0; r_id < m_rule2info.size(); ++r_id) {
                out << "inst " << r_id << ": "
                    << mk_pp(m_rule2info[r_id].m_body, m) << std::endl;
                vector<expr_ref_vector> const& preds_vector = m_rule2info[r_id].m_preds;
                for (unsigned i = 0; i < preds_vector.size(); ++i) {
                    out << "  #" << i << "(" << preds_vector[i].size() << "): ";
                    print_expr_ref_vector(out, preds_vector[i]);
                }
            }
            out << "rule dependency" << std::endl;
            for (func_decl2uints::iterator it = m_func_decl_body2rules.begin(),
                     end = m_func_decl_body2rules.end(); it != end; ++it) {
                out << mk_pp(it->m_key, m) << ": " << it->m_value << std::endl;
            }
        }

        void print_inference_state(std::ostream& out) const {
            out << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" <<
                std::endl << "node counter " << m_node2info.size() << std::endl;
            for (unsigned i = 0; i < m_node2info.size(); ++i) {
                node_info const& node = m_node2info[i];
                out << "node " << i << " "
                    << mk_pp(node.m_func_decl, m) << " [" << node.m_cube << "] "
                    << node.m_parent_rule << " (" << node.m_parent_nodes << ")"
                    << std::endl;
            }
            for (func_decl2node_set::iterator
                it = m_func_decl2max_reach_node_set.begin(),
                end = m_func_decl2max_reach_node_set.end();
                it != end; ++it) {
                out << "max reached nodes " << mk_pp(it->m_key, m) << " "
                    << it->m_value << std::endl;
            }
            out << "worklist " << m_node_worklist << std::endl
                << "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" << std::endl;
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
inline std::ostream& operator<<(std::ostream& out, const vector<T>& v) {
    unsigned size = v.size();
    if (size > 0) {
        out << v[0];
        for (unsigned i = 1; i < size; ++i) out << "," << v[i];
    }
    return out;
}
