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
#include "predabst_rule.h"
#include "predabst_input.h"
#include "predabst_core.h"
#include "predabst_context.h"
#include "dl_context.h"
#include "unifier.h"
#include "reg_decl_plugins.h"
#include "substitution.h"
#include "smt_kernel.h"
#include "smt_solver.h"
#include "model_evaluator.h"
#include "scoped_proof.h"
#include "dl_transforms.h"
#include "fixedpoint_params.hpp"
#include "iz3mgr.h"
#include "iz3interp.h"

namespace datalog {

    struct name_app {
        unsigned        m_name;
        expr_ref_vector m_args;
        name_app(unsigned name, expr_ref_vector const& args) :
            m_name(name),
            m_args(args) {}
        friend std::ostream& operator<<(std::ostream& out, name_app const& app) {
            out << app.m_name << "(" << app.m_args << ")";
            return out;
        }
    };

    struct core_clause {
        name_app         m_head;
        expr_ref_vector  m_interp_body;
        vector<name_app> m_uninterp_body;
        core_clause(name_app const& head, expr_ref_vector const& interp_body, vector<name_app> const& uninterp_body) :
            m_head(head),
            m_interp_body(interp_body),
            m_uninterp_body(uninterp_body) {}
        friend std::ostream& operator<<(std::ostream& out, core_clause const& clause) {
            out << clause.m_head << " :- " << clause.m_interp_body << ", " << clause.m_uninterp_body;
            return out;
        }
    };

    struct core_clause_solution {
        name_app m_head;
        expr_ref m_body;
        core_clause_solution(name_app const& head, expr_ref const& body) :
            m_head(head),
            m_body(body) {}
        friend std::ostream& operator<<(std::ostream& out, core_clause_solution const& solution) {
            out << solution.m_head << " := " << solution.m_body;
            return out;
        }
    };

    typedef vector<core_clause> core_clauses; // just a sequence; the index has no meaning
    typedef vector<core_clause_solution> core_clause_solutions; // ditto

    class predabst::imp {
        struct stats : private predabst_core::stats, private predabst_input::stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }

			// Overall statistics.
            unsigned m_num_refinement_iterations;
            unsigned m_num_template_instantiations;

            // Statistics about refinement.
            unsigned m_num_predicates_added;
            unsigned m_num_predicates_added_query_naming;

			void update(statistics& st) {
				predabst_core::stats::update(st);
				predabst_input::stats::update(st);
#define UPDATE_STAT(NAME) st.update(#NAME, m_ ## NAME)
				UPDATE_STAT(num_refinement_iterations);
				UPDATE_STAT(num_template_instantiations);
				UPDATE_STAT(num_predicates_added);
				UPDATE_STAT(num_predicates_added_query_naming);
			}
        };

        ast_manager&                  m;             // manager for ASTs. It is used for managing expressions
		mutable subst_util            m_subst;
        fixedpoint_params const&      m_fp_params;
		mutable smt::kernel* volatile m_current_solver;
        bool volatile                 m_cancel;      // Boolean flag to track external cancelation.
		model_ref                     m_model;
        mutable stats                 m_stats;       // statistics information specific to the predabst module.
		
		scoped_ptr<predabst_input>    m_input;
		expr_ref_vector               m_template_params;
		expr_ref_vector               m_template_param_values;
	    expr_ref_vector               m_template_constraint_vars;
        expr_ref_vector               m_template_constraints;

        struct core_tree_info {
            unsigned m_count;
            core_tree_info() :
                m_count(0) {}
        };

        struct core_tree_wf_info {
            expr_ref m_bound;
            expr_ref m_decrease;
            core_tree_wf_info(ast_manager& m) :
                m_bound(m),
                m_decrease(m) {}
        };

    public:
        imp(ast_manager& m, fixedpoint_params const& fp_params) :
            m(m),
			m_subst(m),
            m_fp_params(fp_params),
            m_cancel(false),
			m_current_solver(NULL),
			m_template_params(m),
            m_template_param_values(m),
            m_template_constraints(m),
            m_template_constraint_vars(m) {

            reg_decl_plugins(m);
        }

		lbool query(rule_set& rules) {
			m_input = make_predabst_input(rules, m_fp_params);

			for (unsigned i = 0; i < m_input->m_template_vars.size(); ++i) {
				m_template_params.push_back(m.mk_fresh_const("p", get_sort(m_input->m_template_vars.get(i))));
			}

			for (unsigned i = 0; i < m_input->m_symbols.size(); ++i) {
				symbol_info* si = m_input->m_symbols[i];
				for (unsigned j = 0; j < si->m_initial_preds.size(); ++j) {
					maybe_add_pred(si, expr_ref(si->m_initial_preds.get(j), m));
				}
			}

            lbool result = abstract_check_refine();
//#ifdef Z3DEBUG
			if ((result == l_false) && !check_solution(rules)) {
				throw default_exception("check_solution failed");
			}
//#endif

			return result;
        }

        void cancel() {
			// >>> atomic
            m_cancel = true;
			smt::kernel* current_solver = m_current_solver;
			if (current_solver) {
				current_solver->cancel();
			}
        }

        void cleanup() {
			// >>> atomic
			CASSERT("predabst", !m_current_solver);
			m_cancel = false;
		}

        void reset_statistics() {
            m_stats.reset();
        }

        void collect_statistics(statistics& st) const {
			m_stats.update(st);
        }

        void display_certificate(std::ostream& out) const {
            // TBD hmm?
            STRACE("predabst", tout << "inside display_certificate\n";);
            expr_ref ans = get_answer();
            out << ans << "\n";
        }

        expr_ref get_answer() const {
            // TBD hmm?
            return expr_ref(m.mk_true(), m);
        }

        model_ref get_model() const {
			return m_model;
        }

    private:
        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) covering all the variables used by r, which maps the variables
        // used as head arguments to hvars, and maps all variables that do not
        // appear in the head to fresh constants.
        expr_ref_vector get_subst_vect(rule_info const* ri, expr_ref_vector const& hvars, expr_ref_vector const& hvalues, vector<expr_ref_vector> const& bvalues, char const* prefix, expr_ref_vector& unification_terms) const {
            used_vars used = ri->get_used_vars();

            expr_ref_vector rule_subst(m);
            rule_subst.reserve(used.get_max_found_var_idx_plus_1());

            // Variables that appear bare in the non-explicit head are mapped to the first corresponding argument.
            vector<bool> constraint_needed;
            expr_ref_vector head_args = ri->get_abstracted_args();
            CASSERT("predabst", head_args.size() == hvars.size());
            for (unsigned i = 0; i < head_args.size(); ++i) {
                bool assigned = false;
                if (is_var(head_args.get(i))) {
                    unsigned idx = to_var(head_args.get(i))->get_idx();
                    CASSERT("predabst", idx < rule_subst.size());
                    if (!rule_subst.get(idx)) {
                        rule_subst[idx] = hvars.get(i);
                        assigned = true;
                    }
                }
                constraint_needed.push_back(!assigned);
            }

            // Variables that appear bare in the explicit head or body are mapped to the first corresponding value.
            vector<bool> head_exp_constraint_needed;
            expr_ref_vector head_eargs = ri->get_explicit_args();
            CASSERT("predabst", head_eargs.size() == hvalues.size());
            for (unsigned i = 0; i < head_eargs.size(); ++i) {
                bool assigned = false;
                if (is_var(head_eargs.get(i))) {
                    unsigned idx = to_var(head_eargs.get(i))->get_idx();
                    CASSERT("predabst", idx < rule_subst.size());
                    if (!rule_subst.get(idx)) {
                        rule_subst[idx] = hvalues.get(i);
                        assigned = true;
                    }
                }
                head_exp_constraint_needed.push_back(!assigned);
            }

            vector<vector<bool> > body_exp_constraint_needed;
            body_exp_constraint_needed.resize(ri->get_tail_size());
            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                expr_ref_vector body_eargs = ri->get_explicit_args(i);
                CASSERT("predabst", body_eargs.size() == bvalues.get(i).size());
                for (unsigned j = 0; j < body_eargs.size(); ++j) {
                    bool assigned = false;
                    if (is_var(body_eargs.get(j))) {
                        unsigned idx = to_var(body_eargs.get(j))->get_idx();
                        CASSERT("predabst", idx < rule_subst.size());
                        if (!rule_subst.get(idx)) {
                            rule_subst[idx] = bvalues.get(i).get(j);
                            assigned = true;
                        }
                    }
                    body_exp_constraint_needed.get(i).push_back(!assigned);
                }
            }

            // Other variables are mapped to fresh constants.
            for (unsigned i = 0; i < used.get_max_found_var_idx_plus_1(); ++i) {
                if (!rule_subst.get(i)) {
                    sort* s = used.get(i);
                    if (s) {
                        rule_subst[i] = m.mk_fresh_const(prefix, s);
                    }
                }
            }

            // Generate constraints for all head or explicit body argument positions that were not mapped directly to the corresponding argument.
            CASSERT("predabst", unification_terms.empty());
            for (unsigned i = 0; i < head_args.size(); ++i) {
                if (constraint_needed[i]) {
                    unification_terms.push_back(m.mk_eq(m_subst.apply(head_args.get(i), rule_subst), hvars.get(i)));
                }
            }

            for (unsigned i = 0; i < head_eargs.size(); ++i) {
                if (head_exp_constraint_needed[i]) {
                    unification_terms.push_back(m.mk_eq(m_subst.apply(head_eargs.get(i), rule_subst), hvalues.get(i)));
                }
            }

            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                expr_ref_vector body_eargs = ri->get_explicit_args(i);
                CASSERT("predabst", body_eargs.size() == bvalues.get(i).size());
                for (unsigned j = 0; j < body_eargs.size(); ++j) {
                    if (body_exp_constraint_needed[i][j]) {
                        unification_terms.push_back(m.mk_eq(m_subst.apply(body_eargs.get(j), rule_subst), bvalues.get(i).get(j)));
                    }
                }
            }

            return rule_subst;
        }

        expr_ref_vector get_rule_terms(rule_info const* ri, expr_ref_vector const& hargs, expr_ref_vector const& hvalues, vector<expr_ref_vector> const& bvalues, expr_ref_vector& rule_subst, bool substitute_template_params = true) const {
            CASSERT("predabst", rule_subst.empty());
            expr_ref_vector unification_terms(m);
            rule_subst.swap(get_subst_vect(ri, hargs, hvalues, bvalues, "s", unification_terms));
			expr_ref_vector const& temp_params = substitute_template_params ? m_template_param_values : m_template_params;
            expr_ref_vector body_terms = m_subst.apply(ri->get_body(temp_params, m_subst), rule_subst);
            return vector_concat(unification_terms, body_terms);
        }

        void set_logic(smt::kernel& solver) const {
            if (m_fp_params.solver_logic().bare_str()) { // >>> does this make sense?
                bool result = solver.set_logic(m_fp_params.solver_logic());
                CASSERT("predabst", result);
            }
        }

		model_ref make_model(predabst_core const& core) const {
			model_ref md = alloc(model, m);
			// templated predicate symbols are instantiated
			for (unsigned i = 0; i < m_input->m_templates.size(); ++i) {
				template_info const* ti = m_input->m_templates[i];
				expr_ref body = ti->get_body_from_extras(m_template_param_values, m_subst);
				register_decl(md, ti->m_fdecl, body);
			}
			// other predicate symbols are concretized
			for (unsigned i = 0; i < m_input->m_symbols.size(); ++i) {
				symbol_info const* si = m_input->m_symbols[i];
				// Note that the generated model must be in terms of
				// get_arg_vars(si->m_fdecl); we generate the model in terms of
				// si->m_vars, which we assume to be the same.
				expr_ref body = core.get_model(si);
				register_decl(md, si->m_fdecl, body);
			}
			return md;
		}

        lbool abstract_check_refine() {
			unsigned refine_count = 0;
			while (true) {
				if (!instantiate_templates()) {
					STRACE("predabst", tout << "Template instantiation unsuccessful: result is UNSAT\n";);
					return l_true;
				}

				predabst_core core(m_input->m_symbols, m_input->m_rules, m_template_param_values, m_fp_params, m);

				// The only things that change on subsequent iterations of this loop are
				// the predicate lists
				// (m_func_decl2symbol::m_preds) and template instances.  The latter can have an
				// effect on the execution of the algorithm via the initial nodes
				// set up by initialize_abs.
				while (true) {
					m_stats.m_num_refinement_iterations++;
					STRACE("predabst", print_refinement_state(tout, refine_count););

					// >>> accumulate the statistics from the core
					if (core.find_solution(refine_count)) {
						STRACE("predabst", tout << "Solution found: result is SAT\n";);
						m_model = make_model(core);
						return l_false;
					}
					else if (!m_fp_params.use_refinement()) {
						STRACE("predabst", tout << "No solution found: result is UNSAT\n";);
						return l_true;
					}
					else {
						// Our attempt to find a solution failed and we want to try refinement.
						refine_count++;
						counterexample_kind error_kind = core.get_counterexample_kind();
						node_info const* error_node = core.get_counterexample();
						core_tree_info core_info;
						core_tree_wf_info core_info_wf(m);
						expr_ref_vector error_args(m);
						if (error_node->m_symbol) {
							error_args.swap(error_node->m_symbol->get_fresh_args("r"));
						}
						if (not_reachable_without_abstraction(error_node, error_args, core_info)) {
							// The problem node isn't reachable without abstraction.
							// We need to refine the abstraction and retry.
							if (!refine_predicates_not_reachable(error_node, error_args, core_info)) {
								STRACE("predabst", tout << "Predicate refinement unsuccessful: result is UNKNOWN\n";);
								return l_undef;
							}

							STRACE("predabst", tout << "Predicate refinement successful: retrying\n";);
						}
						else if ((error_kind == not_dwf) && wf_without_abstraction(error_node, error_args, core_info_wf)) {
							// The problem node is well-founded without abstraction.
							// We need to refine the abstraction and retry.
							if (!refine_predicates_wf(error_node, error_args, core_info, core_info_wf)) {
								STRACE("predabst", tout << "WF predicate refinement unsuccessful: result is UNKNOWN\n";);
								return l_undef;
							}

							STRACE("predabst", tout << "WF predicate refinement successful: retrying\n";);
						}
						else {
							// The problem persists without abstraction.  Unless
							// we can refine the templates, we have a proof of
							// unsatisfiability.
							constrain_templates(error_node, error_args, error_kind);
							STRACE("predabst", tout << "Attempting template refinement\n";);
							break;
						}
					}
				}
			}
        }

		lbool check(smt::kernel* solver, unsigned num_assumptions = 0, expr* const* assumptions = 0) const {
			{
				// >>> atomic
				if (m_cancel) {
					STRACE("predabst", tout << "Canceled!\n";);
					throw default_exception("canceled");
				}
				m_current_solver = solver;
			}
			lbool result = solver->check(num_assumptions, assumptions);
			{
				// >>> atomic
				m_current_solver = NULL;
				if (m_cancel) {
					solver->reset_cancel();
					STRACE("predabst", tout << "Canceled!\n";);
					throw default_exception("canceled");
				}
			}
			if (result == l_undef) {
				STRACE("predabst", tout << "Solver failed with " << solver->last_failure_as_string() << "\n";);
				throw default_exception("(underlying-solver " + solver->last_failure_as_string() + ")");
			}
			return result;
		}

        expr_ref model_eval_app(model_ref const& md, app const* app) const {
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
            return m_subst.apply(exp, subst);
        }

        expr_ref ground(expr_ref const& exp, char const* prefix) const {
            ptr_vector<sort> sorts;
            get_free_vars(exp, sorts);
            expr_ref_vector subst(m);
            subst.reserve(sorts.size());
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (sorts[i]) {
                    subst[i] = m.mk_fresh_const(prefix, sorts[i]);
                }
            }
            return m_subst.apply(exp, subst);
        }

        bool check_solution(rule_set const& rules) const {
            smt_params new_param;
            smt::kernel solver(m, new_param);
            set_logic(solver);
			for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
				rule* r = rules.get_rule(i);
                unsigned usz = r->get_uninterpreted_tail_size();
                unsigned tsz = r->get_tail_size();
                expr_ref_vector body_exp_terms(m, tsz - usz, r->get_expr_tail() + usz);
                for (unsigned j = 0; j < usz; ++j) {
                    body_exp_terms.push_back(model_eval_app(m_model, r->get_tail(j)));
                }
                expr_ref body_exp = mk_conj(body_exp_terms);
                expr_ref head_exp(m);
				if (rules.is_output_predicate(r->get_decl())) {
					head_exp = m.mk_false();
				}
				else {
					head_exp = model_eval_app(m_model, r->get_head());
				}
                solver.assert_expr(ground(expr_ref(m.mk_and(body_exp, mk_not(head_exp)), m), "c"));
            }
			if (check(&solver) != l_false) {
				STRACE("predabst", tout << "Solution does not satisfy rules\n";);
				return false;
			}
			else {
				return true;
			}
        }

        bool not_reachable_without_abstraction(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info& core_info) const {
            STRACE("predabst", tout << "Determining reachability of node " << root_node << " without abstraction\n";);
            bool result = mk_core_tree(root_node, root_args, core_info);
            STRACE("predabst", tout << "Node " << root_node << " is " << (result ? "not " : "") << "reachable without abstraction\n";);
            return result;
        }

        bool refine_predicates_not_reachable(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info const& core_info) {
            vector<symbol_info*> name2func_decl;
            expr_ref last_clause_body(m);
            core_clauses clauses = mk_core_clauses(root_node, root_args, core_info, name2func_decl, &last_clause_body);
            core_clauses clauses2 = cone_of_influence(clauses, last_clause_body);
            core_clause_solutions solutions = solve_core_clauses(clauses2);
            return refine_preds(solutions, name2func_decl);
        }

        bool wf_without_abstraction(node_info const* root_node, expr_ref_vector const& root_args, core_tree_wf_info& core_wf_info) const {
            STRACE("predabst", tout << "Determining well-foundedness of node " << root_node << " without abstraction\n";);
            CASSERT("predabst", root_node->m_symbol->m_is_dwf);
            expr_ref actual_cube = mk_leaves(root_node, root_args);
            quantifier_elimination(root_args, actual_cube);
            bool result = well_founded(root_args, actual_cube, &core_wf_info.m_bound, &core_wf_info.m_decrease);
            STRACE("predabst", tout << "Node " << root_node << " is " << (result ? "" : "not ") << "well-founded without abstraction\n";);
            return result;
        }

        bool refine_predicates_wf(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info const& core_info, core_tree_wf_info const& core_wf_info) {
            vector<symbol_info*> name2func_decl;
            core_clauses clauses = mk_core_clauses(root_node, root_args, core_info, name2func_decl);
            bool result = false;
            core_clauses bound_clauses = cone_of_influence_with_extra(clauses, core_wf_info.m_bound);
            core_clause_solutions bound_solutions = solve_core_clauses(bound_clauses);
            result |= refine_preds(bound_solutions, name2func_decl);
            core_clauses decrease_clauses = cone_of_influence_with_extra(clauses, core_wf_info.m_decrease);
            core_clause_solutions decrease_solutions = solve_core_clauses(decrease_clauses);
            result |= refine_preds(decrease_solutions, name2func_decl);
            return result;
        }

        bool refine_preds(core_clause_solutions const& solutions, vector<symbol_info*> const& name2func_decl) {
            unsigned new_preds_added = 0;
            for (unsigned i = 0; i < solutions.size(); ++i) {
                core_clause_solution const& solution = solutions.get(i);
                CASSERT("predabst", solution.m_head.m_name < name2func_decl.size());
                symbol_info* si = name2func_decl[solution.m_head.m_name];
                CASSERT("predabst", si);
                expr_ref pred(replace_pred(solution.m_head.m_args, si->m_abstracted_vars, solution.m_body), m);
                new_preds_added += maybe_add_pred(si, pred);
            }
            return (new_preds_added > 0);
        }

        unsigned maybe_add_pred(symbol_info* si, expr_ref const& p) {
            expr_ref pred = normalize_pred(p, si->m_abstracted_vars);
            if (m.is_true(pred) || m.is_false(pred)) {
                STRACE("predabst", tout << "Ignoring predicate " << pred << " for " << si << "\n";);
                return 0;
            }
            else if (si->m_preds.contains(pred)) {
                STRACE("predabst", tout << "Predicate " << pred << " for " << si << " is already present\n";);
                return 0;
            }
            else {
                unsigned new_preds_added = 1;
                add_pred(si, pred);
                m_stats.m_num_predicates_added++;
                if (m_fp_params.use_query_naming() && new_preds_added) {
                    var_ref_vector used_vars = to_vars(get_all_vars(pred));
                    func_decl_ref_vector used_var_names(m);
                    for (unsigned i = 0; i < used_vars.size(); ++i) {
						var_ref var(used_vars.get(i), m);
                        unsigned j = var->get_idx();
                        if (!si->m_var_names.get(j)) {
                            STRACE("predabst", tout << "Don't have name for variable " << var << " used in predicate " << p << " for " << si << "\n";);
                            return new_preds_added;
                        }
                        used_var_names.push_back(si->m_var_names.get(j));
                    }
                    for (unsigned i = 0; i < m_input->m_symbols.size(); ++i) {
                        symbol_info* fi2 = m_input->m_symbols[i];
                        if (fi2 == si) {
                            continue;
                        }
                        if (vector_subset(used_var_names, fi2->m_var_names)) {
                            var_ref_vector used_vars2(m);
                            for (unsigned j = 0; j < used_var_names.size(); ++j) {
                                unsigned k = vector_find(fi2->m_var_names, used_var_names.get(j));
                                used_vars2.push_back(fi2->m_abstracted_vars.get(k)); // >>> wrong!!!
                            }
                            new_preds_added++;
                            add_pred(fi2, m_subst.apply(pred, m_subst.build(used_vars, used_vars2)));
                            m_stats.m_num_predicates_added_query_naming++;
                        }
                    }
                }
                return new_preds_added;
            }
        }

        void add_pred(symbol_info* si, expr_ref const& pred) {
            CASSERT("predabst", !si->m_preds.contains(pred));
            CASSERT("predabst", vector_intersection(si->m_explicit_vars, to_vars(get_all_vars(pred))).empty());
            STRACE("predabst", tout << "Found new predicate " << pred << " for " << si << "\n";);
            si->m_preds.push_back(pred);
        }

        void constrain_templates(node_info const* error_node, expr_ref_vector const& error_args, counterexample_kind error_kind) {
            expr_ref cs = mk_leaves(error_node, error_args, false);
            quantifier_elimination(vector_concat(error_args, m_template_params), cs);

            expr_ref to_solve(m);
            if (error_kind == reached_query) {
                STRACE("predabst", tout << "Refining templates (reached query)\n";);
                to_solve = template_constraint_reached_query(cs);
            }
            else {
                CASSERT("predabst", error_kind == not_dwf);
                STRACE("predabst", tout << "Refining templates (not well-founded)\n";);
                to_solve = template_constraint_not_wf(error_args, cs);
            }

            m_template_constraints.push_back(to_solve);

            expr_ref_vector evars = get_all_vars(cs);
            for (unsigned i = 0; i < error_args.size(); ++i) {
                evars.erase(error_args.get(i));
            }
            for (unsigned i = 0; i < m_template_params.size(); ++i) {
                evars.erase(m_template_params.get(i));
            }

            m_template_constraint_vars.append(error_args);
            m_template_constraint_vars.append(evars);
        }

        expr_ref template_constraint_reached_query(expr_ref const& cs) {
            return expr_ref(m.mk_not(cs), m);
        }

        expr_ref template_constraint_not_wf(expr_ref_vector const& args, expr_ref const& cs) {
            expr_ref bound(m);
            expr_ref decrease(m);
            well_founded_bound_and_decrease(args, bound, decrease);
            return expr_ref(m.mk_or(m.mk_not(cs), m.mk_and(bound, decrease)), m);
        }

        unsigned reduce_unsat(smt::kernel& solver, expr* const* assumptions, unsigned lo, unsigned hi, obj_map<expr, unsigned> const& assumption_to_index) const {
            unsigned n;
            if (m_fp_params.prune_bsearch()) {
                n = 0;
                unsigned unsat_core_size = solver.get_unsat_core_size();
                for (unsigned i = 0; i < unsat_core_size; ++i) {
                    n = std::max(n, assumption_to_index.find(solver.get_unsat_core_expr(i)) + 1);
                }
            }
            else {
                n = hi;
            }
            CASSERT("predabst", n > lo);
            CASSERT("predabst", n <= hi);
            CASSERT("predabst", check(&solver, n, assumptions) != l_true);
            return n;
        }

        // Returns the smallest n such that the conjunction of the first n
        // assumptions is unsatisfiable, if any; otherwise returns the
        // number of assumptions.
        unsigned find_unsat_prefix(smt::kernel& solver, expr* const* assumptions, unsigned lo, unsigned hi, obj_map<expr, unsigned> const& assumption_to_index) const {
            // pre-conditions:
            // -  conjunction of first lo terms (sequence e_0 .. e_{lo-1}) is sat
            // -  conjunction of first hi terms (sequence e_0 .. e_{hi-1}) is either unsat, or else hi = #terms
            CASSERT("predabst", lo <= hi);
            if ((lo == hi) || (lo + 1 == hi)) {
                return hi;
            }
            unsigned mid = lo + ((hi - lo) * m_fp_params.bsearch_mid_numerator()) / m_fp_params.bsearch_mid_denominator();
            CASSERT("predabst", lo < mid);
            CASSERT("predabst", mid < hi);
            if (check(&solver, mid, assumptions) != l_true) {
                mid = reduce_unsat(solver, assumptions, lo, mid, assumption_to_index);
                return find_unsat_prefix(solver, assumptions, lo, mid, assumption_to_index);
            }
            else {
                return find_unsat_prefix(solver, assumptions, mid, hi, assumption_to_index);
            }
        }

		bool mk_core_tree(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info &core_info) const {
			smt_params new_param;
#ifndef _TRACE
			new_param.m_model = false;
#endif
            smt::kernel solver(m, new_param);
            set_logic(solver);

            expr_ref_vector terms = get_conj_terms(mk_leaves(root_node, root_args));

            expr_ref_vector guard_vars(m);
            obj_map<expr, unsigned> guard_var_to_index;
            unsigned lo = 0;
            unsigned hi = 0;
            unsigned increment = m_fp_params.unsat_prefix_initial_size();
            while (hi < terms.size()) {
                lo = hi;
                hi += increment;
                if (hi > terms.size()) {
                    hi = terms.size();
                }
                for (unsigned i = lo; i < hi; ++i) {
                    expr_ref c(m.mk_fresh_const("cv", m.mk_bool_sort()), m);
                    guard_vars.push_back(c);
                    guard_var_to_index.insert(c, i);
                    if (!m.is_true(terms.get(i))) {
                        expr_ref e(m.mk_iff(terms.get(i), c), m);
                        solver.assert_expr(e);
                    }
                }
                if (check(&solver, hi, guard_vars.c_ptr()) != l_true) {
                    hi = reduce_unsat(solver, guard_vars.c_ptr(), lo, hi, guard_var_to_index);
                    break;
                }
                increment *= m_fp_params.unsat_prefix_growth_factor();
            }
            // first 'lo' are sat; first 'hi' are unsat, or else hi = #terms
            core_info.m_count = find_unsat_prefix(solver, guard_vars.c_ptr(), lo, hi, guard_var_to_index);
            CASSERT("predabst", core_info.m_count <= guard_vars.size());

            if ((core_info.m_count == terms.size()) &&
                (check(&solver, guard_vars.size(), guard_vars.c_ptr()) == l_true)) {
                STRACE("predabst", {
					tout << "Example model:\n";
					model_ref modref;
                    solver.get_model(modref);
					CASSERT("predabst", modref);
					for (unsigned i = 0; i < modref->get_num_constants(); ++i) {
						func_decl_ref c(modref->get_constant(i), m);
						if (!guard_vars.contains(m.mk_const(c))) {
							expr_ref e(modref->get_const_interp(c), m);
							tout << "  " << c->get_name() << " has value " << e << "\n";
						}
					}
				});
                return false;
            }
            else {
                return true;
            }
        }

        core_clauses mk_core_clauses(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info const& core_info, vector<symbol_info*>& name2func_decl, expr_ref* last_clause_body = NULL) const {
            STRACE("predabst", tout << "Building clauses from " << core_info.m_count << " assertions\n";);
            core_clauses clauses;

            unsigned last_count = core_info.m_count;
            unsigned count = 0;

            vector<name_app> todo;
            vector<node_info const*> name2node;
            name2node.push_back(root_node);
            name2func_decl.push_back(const_cast<symbol_info*>(root_node->m_symbol));
            todo.push_back(name_app(0, root_args));

            while (!todo.empty()) {
                name_app item = todo.back();
                todo.pop_back();

                expr_ref_vector cs(m);
                vector<name_app> parents;

                node_info const* node = name2node[item.m_name];
                rule_info const* ri = node->m_parent_rule;

                if (count < last_count) {
                    expr_ref_vector const& hvalues = node->m_values;
                    vector<expr_ref_vector> bvalues;
                    for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                        node_info const* qnode = node->m_parent_nodes[i];
                        bvalues.push_back(qnode->m_values);
                    }
                    expr_ref_vector rule_subst(m);
                    expr_ref_vector terms = get_rule_terms(ri, item.m_args, hvalues, bvalues, rule_subst);
                    for (unsigned i = 0; i < terms.size(); ++i) {
                        cs.push_back(terms.get(i));
                        count++;
                        if (count == last_count) {
                            if (last_clause_body) {
                                *last_clause_body = cs.get(cs.size() - 1);
                            }
                            break;
                        }
                    }

                    if (count < last_count) {
                        for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                            node_info const* qnode = node->m_parent_nodes[i];
                            unsigned qname = name2node.size();
                            // Ensure that all the qargs are (distinct) uninterpreted constants.
                            expr_ref_vector pargs = m_subst.apply(ri->get_abstracted_args(i), rule_subst);
                            expr_ref_vector qargs(m);
                            for (unsigned j = 0; j < pargs.size(); ++j) {
                                expr_ref arg_j(pargs.get(j), m);
                                if (is_uninterp_const(arg_j) && !qargs.contains(arg_j)) {
                                    qargs.push_back(arg_j);
                                }
                                else {
                                    expr_ref f(m.mk_fresh_const("x", get_sort(arg_j)), m);
                                    qargs.push_back(f);
                                    expr_ref constraint(m.mk_eq(f, arg_j), m);
                                    cs.push_back(constraint);
                                }
                            }
                            name2node.push_back(qnode);
                            name2func_decl.push_back(const_cast<symbol_info*>(qnode->m_symbol));
                            todo.push_back(name_app(qname, qargs));
                            parents.push_back(name_app(qname, qargs));
                        }
                    }
                }

                core_clause clause(item, cs, parents);
                STRACE("predabst", tout << "Adding clause for " << node->m_symbol << ": " << clause << "\n";);
                clauses.push_back(clause);
            }

            CASSERT("predabst", count == last_count);
            return clauses;
        }

        core_clauses cone_of_influence(core_clauses const& clauses, expr_ref const& critical) const {
            if (!m_fp_params.use_coi()) {
                STRACE("predabst", tout << "Skipping cone of influence\n";);
                return clauses;
            }

            STRACE("predabst", tout << "Computing cone of influence for expression " << critical << "\n";);
                
            // Find connected components for the graph whose vertices are
            // the variables used by the clauses, and whose has an edge from
            // a to b if a and b appear within an atomic expression in the
            // clauses.  An expression belongs to the same component as the
            // variables it involves.
            obj_map<expr, unsigned> component_map;
            unsigned num_components = 0;
            for (unsigned i = 0; i < clauses.size(); ++i) {
                core_clause clause = clauses[i];
                for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
                    expr_ref e(clause.m_interp_body.get(j), m);
                    if (!component_map.contains(e)) {
                        expr_ref_vector vars = get_all_vars(e);
                        unsigned component;
                        bool found_component = false;
                        for (unsigned k = 0; k < vars.size(); ++k) {
                            expr_ref v(vars.get(k), m);
                            if (component_map.contains(v)) {
                                if (found_component) {
                                    unsigned component2 = component_map.find(v);
                                    // Variables from both component and component2
                                    // appear within e; merge the components.
                                    for (obj_map<expr, unsigned>::iterator it = component_map.begin(); it != component_map.end(); ++it) {
                                        if (it->m_value == component2) {
                                            it->m_value = component;
                                        }
                                    }
                                }
                                else {
                                    component = component_map.find(v);
                                    found_component = true;
                                }
                            }
                        }
                        if (!found_component) {
                            // None of the variables of e is in a component
                            // yet, so create a new component to hold them.
                            component = num_components++;
                        }
                        // Map e and all its variables to this component.
                        component_map.insert(e, component);
                        for (unsigned k = 0; k < vars.size(); ++k) {
                            expr_ref v(vars.get(k), m);
                            component_map.insert_if_not_there(v, component);
                        }
                    }
                }
            }

            STRACE("predabst", {
                for (obj_map<expr, unsigned>::iterator it = component_map.begin(); it != component_map.end(); ++it) {
                    tout << "  " << expr_ref(it->m_key, m) << " -> component " << it->m_value << "\n";
                }
            });

            // Find the important component, namely the one containing the
            // critical expression.
            unsigned important = component_map.find(critical);

            // Copy the clauses, eliminating unimportant expressions.
            core_clauses clauses2;
            for (unsigned i = 0; i < clauses.size(); ++i) {
                core_clause const& clause = clauses[i];
                expr_ref_vector const& interp_body = clause.m_interp_body;
                expr_ref_vector interp_body2(m);
                for (unsigned j = 0; j < interp_body.size(); ++j) {
                    expr_ref e(interp_body.get(j), m);
                    if (component_map.find(e) == important) {
                        interp_body2.push_back(e);
                    }
                }
                core_clause clause2(clause.m_head, interp_body2, clause.m_uninterp_body);
                STRACE("predabst", tout << "  rewriting clause " << i << ": " << clause << " -> " << clause2 << "\n";);
                clauses2.push_back(clause2);
            }
            return clauses2;
        }

        core_clauses cone_of_influence_with_extra(core_clauses const& clauses, expr_ref const& extra) const {
            vector<name_app> root_app;
            root_app.push_back(clauses[0].m_head);

            unsigned name2 = clauses.size();
            name_app head_app(name2, expr_ref_vector(m));

            expr_ref_vector interp_body(m);
            interp_body.push_back(mk_not(extra));

            core_clause extra_clause(head_app, interp_body, root_app);
            STRACE("predabst", tout << "Adding extra clause: " << extra_clause << "\n";);

            core_clauses clauses2;
            clauses2.push_back(extra_clause);
            clauses2.append(clauses);

            return cone_of_influence(clauses2, mk_not(extra));
        }

        core_clause_solutions solve_core_clauses(core_clauses const& clauses) const {
			vector<unsigned> assertion_start_index;
			expr_ref_vector assertions(m);
			for (unsigned i = 0; i < clauses.size(); ++i) {
                core_clause const& clause = clauses[i];
				assertion_start_index.push_back(assertions.size());
				for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
					assertions.push_back(clause.m_interp_body[j]);
				}
            }

			expr_ref_vector vars = get_all_vars(mk_conj(assertions));
			vector<linear_inequality> assertion_inequalities;
			for (unsigned i = 0; i < assertions.size(); ++i) {
				assertion_inequalities.push_back(linear_inequality(vars.size(), m));
				if (!assertion_inequalities.back().set_from_expr(to_nnf(expr_ref(assertions.get(i), m)), vars)) { // >>> to_nnf is a bit of a hack; perhaps the elimination of "not" should be put back into set_from_expr
					STRACE("predabst", tout << "Cannot solve clauses: not a system of linear (in)equalities\n";);
					return core_clause_solutions();
				}
			}

            vector<int64> assertion_coeffs;
            get_farkas_coeffs(assertion_inequalities, assertion_coeffs);
			STRACE("predabst", {
				tout << "Farkas coefficients are:\n";
				for (unsigned i = 0; i < assertion_coeffs.size(); ++i) {
					tout << "  " << assertion_coeffs[i] << " @ " << assertion_inequalities[i].to_expr(vars) << "\n";
				}
			});

            vector<linear_inequality> name2solution;
            for (unsigned i = clauses.size() - 1; i > 0; --i) { // skip clause 0
                core_clause const& clause = clauses[i];
                vector<int64> coeffs;
                vector<linear_inequality> inequalities;
                for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
                    coeffs.push_back(assertion_coeffs[assertion_start_index[i] + j]);
					inequalities.push_back(assertion_inequalities[assertion_start_index[i] + j]);
                }
                for (unsigned j = 0; j < clause.m_uninterp_body.size(); ++j) {
                    coeffs.push_back(1);
                    // >>> TODO assert that head and body arguments are distinct uninterpreted constants
                    // >>> TODO assert that the head arguments and the body arguments are the same (otherwise need to do substitution)
                    inequalities.push_back(name2solution.get(clause.m_uninterp_body[j].m_name));
                }
                name2solution.reserve(clause.m_head.m_name + 1, linear_inequality(vars.size(), m));
				name2solution[clause.m_head.m_name].set_from_linear_combination(coeffs, inequalities);
			}

			core_clause_solutions solutions;
			for (unsigned i = 1; i < clauses.size(); ++i) { // skip clause 0
				core_clause const& clause = clauses[i];
				// >>> TODO: assert that body has no uninterpreted constants not in head
				core_clause_solution solution(clause.m_head, name2solution[clause.m_head.m_name].to_expr(vars));
				STRACE("predabst", tout << "Solution for clause " << i << ": " << solution << "\n";);
				solutions.push_back(solution);
			}
			return solutions;
        }

        expr_ref mk_leaves(node_info const* root_node, expr_ref_vector const& root_args, bool substitute_template_params = true) const {
            STRACE("predabst", tout << "Determining reachability criterion for node " << root_node << " without abstraction\n";);
            expr_ref_vector cs(m);

            struct todo_item {
                node_info const* m_node;
                expr_ref_vector  m_args;
                todo_item(node_info const* node, expr_ref_vector const& args) :
                    m_node(node),
                    m_args(args) {}
            };
            vector<todo_item> todo;
            todo.push_back(todo_item(root_node, root_args));

            while (!todo.empty()) {
                todo_item item = todo.back();
                todo.pop_back();

                expr_ref_vector const& args = item.m_args;
                node_info const* node = item.m_node;
                rule_info const* ri = node->m_parent_rule;

                STRACE("predabst", tout << "To reach node " << node << " (" << node->m_symbol << "(" << args << ")) via rule " << ri << " requires:\n";);
                expr_ref_vector const& hvalues = node->m_values;
                vector<expr_ref_vector> bvalues;
                for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                    node_info const* qnode = node->m_parent_nodes[i];
                    bvalues.push_back(qnode->m_values);
                }
                expr_ref_vector rule_subst(m);
                expr_ref_vector terms = get_rule_terms(ri, args, hvalues, bvalues, rule_subst, substitute_template_params);
                STRACE("predabst", tout << "  " << mk_conj(terms) << "\n";);
                cs.append(terms);

                for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                    node_info const* qnode = node->m_parent_nodes[i];
                    expr_ref_vector qargs = m_subst.apply(ri->get_abstracted_args(i), rule_subst);
                    STRACE("predabst", tout << "  reaching node " << qnode << " (" << qnode->m_symbol << "(" << qargs << "))\n";);
                    todo.push_back(todo_item(qnode, qargs));
                }
            }

            return mk_conj(cs);
        }

        bool instantiate_templates() {
            STRACE("predabst", tout << "Instantiating templates using constraints: " << m_template_constraints << "\n";);

            expr_ref_vector constraints(m);
            vector<lambda_info> lambda_infos;
            bool result = mk_exists_forall_farkas(mk_conj(m_template_constraints), m_template_constraint_vars, constraints, lambda_infos, true);
            if (!result) {
                STRACE("predabst", tout << "Failed to convert template constraints\n";);
                return false;
            }

            int max_lambda = m_fp_params.max_lambda();
            expr_ref_vector lambda_constraints = mk_bilinear_lambda_constraints(lambda_infos, max_lambda, m);

            STRACE("predabst", tout << "  constraints: " << constraints << "\n";);
            STRACE("predabst", tout << "  lambda constraint: " << lambda_constraints << "\n";);

            smt_params new_param;
            smt::kernel solver(m, new_param);
            set_logic(solver);
            if (m_input->m_template_extras) {
                solver.assert_expr(m_subst.apply(m_input->m_template_extras, m_subst.build(m_input->m_template_vars, m_template_params)));
            }
            for (unsigned i = 0; i < constraints.size(); ++i) {
                solver.assert_expr(constraints.get(i));
            }
            for (unsigned i = 0; i < lambda_constraints.size(); ++i) {
                solver.assert_expr(lambda_constraints.get(i));
            }
            if (check(&solver) != l_true) {
                STRACE("predabst", tout << "Failed to solve template constraints\n";);
                return false;
            }
            model_ref modref;
            solver.get_model(modref);

            m_template_param_values.reset();
            for (unsigned i = 0; i < m_template_params.size(); ++i) {
                expr_ref param(m_template_params.get(i), m);
                expr_ref param_value(m);
                if (!modref->eval(param, param_value, true)) {
                    return false;
                }
                STRACE("predabst", tout << "Instantiated template parameter " << param << " := " << param_value << "\n";);
                m_template_param_values.push_back(param_value);
            }

            m_stats.m_num_template_instantiations++;
            return true;
        }

        void register_decl(model_ref const& md, func_decl* fdecl, expr_ref const& e) const {
            STRACE("predabst", tout << "Model for " << fdecl->get_name() << "/" << fdecl->get_arity() << " is " << e << "\n";);
            if (fdecl->get_arity() == 0) {
                md->register_decl(fdecl, e);
            }
            else {
                func_interp* finterp = alloc(func_interp, m, fdecl->get_arity());
                finterp->set_else(e);
                md->register_decl(fdecl, finterp);
            }
        }

		void print_refinement_state(std::ostream& out, unsigned refine_count) const {
			out << "=====================================\n";
			out << "State before refinement step " << refine_count << ":\n";
			out << "  Symbols:" << std::endl;
			for (unsigned i = 0; i < m_input->m_symbols.size(); ++i) {
				symbol_info const* si = m_input->m_symbols[i];
				out << "    " << si << " has ";
				if (si->m_preds.empty()) {
					out << "no ";
				}
				out << "predicates " << si->m_preds << std::endl;
			}
			out << "  Template parameter instances:" << std::endl;
			CASSERT("predabst", m_template_params.size() == m_input->m_template_vars.size());
			CASSERT("predabst", m_template_param_values.size() == m_input->m_template_vars.size());
			for (unsigned i = 0; i < m_input->m_template_vars.size(); ++i) {
				expr_ref param(m_template_params.get(i), m);
				expr_ref param_value(m_template_param_values.get(i), m);
				out << "    " << i << ": " << param << " := " << param_value << std::endl;
			}
			out << "  Rule bodies:" << std::endl;
			for (unsigned i = 0; i < m_input->m_rules.size(); ++i) {
				rule_info const* ri = m_input->m_rules[i];
				out << "    " << i << ": " << ri->get_body(m_template_param_values, m_subst) << std::endl;
			}
			out << "=====================================\n";
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
