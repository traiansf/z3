/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

	predabst_core.cpp

Abstract:

	Bounded PREDABST (symbolic simulation using Z3) core.

Author:

	Created by James Lingard (jchl) 2015-06-18.

Revision History:

--*/
#include "predabst_util.h"
#include "farkas_util.h"
#include "predabst_context.h"
#include "predabst_core.h"
#include "uint_set.h"
#include "model_evaluator.h"
#include "smt_params.h"
#include "smt_kernel.h"
#include "simplifier.h"
#include "arith_simplifier_plugin.h"
#include <vector>
#include <map>
#include <algorithm>

namespace datalog {
	class scoped_push {
		smt::kernel& s;
	public:
		scoped_push(smt::kernel& s) : s(s) { s.push(); }
		~scoped_push() { s.pop(1); }
	};

	struct rule_instance_info {
		expr_ref_vector         m_rule_subst;
		smt::kernel*            m_solver;
		expr_ref_vector         m_body;
		expr_ref_vector         m_head_preds;
		expr_ref_vector         m_head_explicit_args;
		vector<bool>            m_head_known_args;
		unsigned                m_num_head_unknown_args;
		vector<expr_ref_vector> m_body_preds;
		vector<expr_ref_vector> m_body_explicit_args;
		vector<vector<bool>>    m_body_known_args;
		bool                    m_unsat;
		rule_instance_info(expr_ref_vector const& rule_subst, smt::kernel* solver, ast_manager& m) :
			m_rule_subst(rule_subst),
			m_solver(solver),
			m_body(m),
			m_head_preds(m),
			m_head_explicit_args(m),
			m_unsat(false) {}
	};

	class predabst_core::imp {
		struct acr_error {
			node_info const*    const m_node;
			counterexample_kind const m_kind;
			acr_error(node_info const* node, counterexample_kind kind) :
				m_node(node),
				m_kind(kind) {}
		};

		vector<rule_info*> const&                     m_rules;
		expr_ref_vector const&                        m_template_param_values;
		obj_map<rule_info const, rule_instance_info*> m_rule_instances;
		vector<node_info*>                            m_nodes;
		obj_map<symbol_info const, node_vector>       m_max_reach_nodes;
		node_vector                                   m_node_worklist;
		counterexample_kind							  m_counterexample_kind;
		node_info const*							  m_counterexample_node;
		smt_params									  m_fparams;     // parameters specific to smt solving
		smt::kernel*								  m_solver;
		mutable simplifier							  m_simplifier;
		fixedpoint_params const&					  m_fp_params;
		mutable stats								  m_stats;
		subst_util									  m_subst;
		ast_manager&								  m;

	public:
		imp(vector<symbol_info*> const& symbols, vector<rule_info*> const& rules, expr_ref_vector const& template_param_values, fixedpoint_params const& fp_params, ast_manager& m) :
			m_rules(rules),
			m_template_param_values(template_param_values),
			m_solver(NULL),
			m_simplifier(m),
			m_fp_params(fp_params),
			m_subst(m),
			m(m) {

			if (m_fp_params.pre_simplify()) {
				basic_simplifier_plugin* bsimp = alloc(basic_simplifier_plugin, m);
				m_simplifier.register_plugin(bsimp);
				m_simplifier.register_plugin(alloc(arith_simplifier_plugin, m, *bsimp, m_fparams));
			}

			m_fparams.m_mbqi = false;
			m_fparams.m_model = false;
			if (m_fp_params.no_simplify()) {
				m_fparams.m_preprocess = false;
			}

			if (!m_fp_params.solver_per_rule()) {
				m_solver = alloc(smt::kernel, m, m_fparams);
				set_logic(m_solver);
			}
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				rule_info const* ri = m_rules[i];
				smt::kernel* solver;
				if (m_fp_params.solver_per_rule()) {
					solver = alloc(smt::kernel, m, m_fparams);
					set_logic(solver);
				}
				else {
					solver = m_solver;
				}
				try {
					m_rule_instances.insert(ri, instantiate_rule(ri, solver));
				}
				catch (...) {
					if (m_fp_params.solver_per_rule()) {
						dealloc(solver);
					}
					dealloc(m_solver);
					throw;
				}
			}

			for (unsigned i = 0; i < symbols.size(); ++i) {
				symbol_info const* si = symbols[i];
				m_max_reach_nodes.insert(si, node_vector());
			}
		}

		~imp() {
			if (!m_fp_params.solver_per_rule()) {
				dealloc(m_solver);
			}
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				rule_info const* ri = m_rules[i];
				if (m_fp_params.solver_per_rule()) {
					dealloc(m_rule_instances[ri]->m_solver);
				}
				dealloc(m_rule_instances[ri]);
			}
			for (unsigned i = 0; i < m_nodes.size(); ++i) {
				dealloc(m_nodes[i]);
			}
		}

		bool find_solution(unsigned refine_count) {
			for (unsigned i = 0; i < m_nodes.size(); ++i) {
				dealloc(m_nodes[i]);
			}
			m_nodes.reset();
			for (obj_map<symbol_info const, node_vector>::iterator it = m_max_reach_nodes.begin(); it != m_max_reach_nodes.end(); ++it) {
				it->m_value.reset();
			}
			m_node_worklist.reset();
			m_counterexample_node = NULL;

			// Set up m_rules for this iteration:
			// for each rule: ground body and instantiate predicates for applications
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				rule_info* ri = m_rules[i];
				instantiate_rule_preds(ri);
			}

			STRACE("predabst", print_instantiated_rules(tout););

			try {
				// initial abstract inference
				STRACE("predabst", tout << "Performing initial inference\n";);
				for (unsigned i = 0; i < m_rules.size(); ++i) {
					rule_info const* ri = m_rules[i];
					if (ri->get_tail_size() == 0) {
						initialize_abs(ri);
					}
				}

				// process worklist
				unsigned infer_count = 0;
				while (!m_node_worklist.empty()) {
					m_stats.m_num_nodes_dequeued++;

					STRACE("predabst", print_inference_state(tout, refine_count, infer_count););
					node_vector::iterator it = m_node_worklist.begin();
					node_info const* node = *it;
					m_node_worklist.erase(it);
					inference_step(node);
					infer_count++;

					if ((m_fp_params.max_predabst_iterations() > 0) &&
						(m_stats.m_num_nodes_dequeued >= m_fp_params.max_predabst_iterations())) {
						STRACE("predabst", tout << "Exceeded maximum number of iterations\n";);
						throw default_exception("exceeded maximum number of iterations");
					}
				}

				// We managed to find a solution.
				return true;
			}
			catch (acr_error const& counterexample) {
				// We failed to find a solution.
				m_counterexample_kind = counterexample.m_kind;
				m_counterexample_node = counterexample.m_node;
				return false;
			}
		}

		expr_ref get_model(symbol_info const* si) const {
			CASSERT("predabst", !m_counterexample_node);
			node_vector const& nodes = m_max_reach_nodes[si];
			expr_ref_vector disj(m);
			for (node_vector::const_iterator it = nodes.begin(); it != nodes.end(); ++it) {
				node_info const* node = *it;
				disj.push_back(node_to_formula(node));
			}
			return mk_disj(disj);
		}

		counterexample_kind get_counterexample_kind() const {
			CASSERT("predabst", m_counterexample_node);
			return m_counterexample_kind;
		}

		node_info const* get_counterexample() const {
			CASSERT("predabst", m_counterexample_node);
			return m_counterexample_node;
		}

	private:
		void set_logic(smt::kernel* solver) const { // >>> copied!
			if (m_fp_params.solver_logic().bare_str()) { // >>> does this make sense?
				bool result = solver->set_logic(m_fp_params.solver_logic());
				CASSERT("predabst", result);
			}
		}

		inline smt::kernel* solver_for(rule_info const* ri) {
			return m_rule_instances[ri]->m_solver;
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
			CASSERT("predabst", cube.size() == preds.size());
			for (unsigned i = 0; i < cube.size(); ++i) {
				if (cube[i]) {
					es.push_back(preds[i]);
				}
			}
			return mk_conj(es);
		}

		void pre_simplify(expr_ref& e) const {
			if (m_fp_params.pre_simplify()) {
				proof_ref pr(m);
				m_simplifier(e, e, pr);
			}
		}

		void pre_simplify(expr_ref_vector& exprs) const {
			for (unsigned i = 0; i < exprs.size(); ++i) {
				expr_ref e(exprs.get(i), m);
				pre_simplify(e);
				exprs[i] = e;
			}
		}

		void invert(expr_ref_vector& exprs) const {
			for (unsigned i = 0; i < exprs.size(); ++i) {
				exprs[i] = m.mk_not(exprs.get(i));
			}
		}

		vector<bool> known_exprs(expr_ref_vector const& exprs) {
			vector<bool> known_exprs;
			for (unsigned i = 0; i < exprs.size(); ++i) {
				bool known = get_all_vars(expr_ref(exprs.get(i), m)).empty();
				known_exprs.push_back(known);
				if (known) {
					m_stats.m_num_known_explicit_arguments++;
				}
			}
			return known_exprs;
		}

		void maybe_make_false(expr_ref_vector& exprs, smt::kernel* solver) const {
			for (unsigned i = 0; i < exprs.size(); ++i) {
				scoped_push _push(*solver);
				solver->assert_expr(exprs.get(i));
				if (check(solver) == l_false) {
					exprs[i] = m.mk_false();
					m_stats.m_num_false_predicates++;
				}
			}
		}

		void maybe_make_true(expr_ref_vector& exprs, smt::kernel* solver) const {
			for (unsigned i = 0; i < exprs.size(); ++i) {
				scoped_push _push(*solver);
				expr_ref e(m.mk_not(exprs.get(i)), m);
				pre_simplify(e);
				solver->assert_expr(e);
				if (check(solver) == l_false) {
					exprs[i] = m.mk_true();
					m_stats.m_num_true_predicates++;
				}
			}
		}

		void assert_guarded_exprs(expr_ref_vector& exprs, smt::kernel* solver) const {
			expr_ref_vector guard_vars(m);
			for (unsigned i = 0; i < exprs.size(); ++i) {
				if (!m.is_false(exprs.get(i)) && !m.is_true(exprs.get(i))) {
					expr_ref g(m.mk_fresh_const("g", m.mk_bool_sort()), m);
					expr_ref e(m.mk_iff(exprs.get(i), g), m);
					STRACE("predabst", tout << "Asserting " << e << "\n";);
					solver->assert_expr(e);
					exprs[i] = g;
				}
			}
		}

		lbool check(smt::kernel* solver, unsigned num_assumptions = 0, expr* const* assumptions = 0) const {
/*
			{
				// >>> atomic
				if (m_cancel) {
					STRACE("predabst", tout << "Canceled!\n";);
					throw default_exception("canceled");
				}
				m_current_solver = solver;
			}
*/
			lbool result = solver->check(num_assumptions, assumptions);
/*
			{
				// >>> atomic
				m_current_solver = NULL;
				if (m_cancel) {
					solver->reset_cancel();
					STRACE("predabst", tout << "Canceled!\n";);
					throw default_exception("canceled");
				}
			}
*/
			if (result == l_undef) {
				STRACE("predabst", tout << "Solver failed with " << solver->last_failure_as_string() << "\n";);
				throw default_exception("(underlying-solver " + solver->last_failure_as_string() + ")");
			}
			return result;
		}

		// Returns a substitution vector mapping each variable used in ri to a
		// fresh constant.
		static expr_ref_vector get_subst_vect_free(rule_info const* ri, char const* prefix, ast_manager& m) {
			expr_ref_vector rule_subst(m);

			used_vars used = ri->get_used_vars();
			rule_subst.reserve(used.get_max_found_var_idx_plus_1());
			for (unsigned i = 0; i < used.get_max_found_var_idx_plus_1(); ++i) {
				sort* s = used.get(i);
				if (s) {
					rule_subst[i] = m.mk_fresh_const(prefix, s);
				}
			}

			return rule_subst;
		}

		rule_instance_info* instantiate_rule(rule_info const* ri, smt::kernel* solver) {
			STRACE("predabst", tout << "Instantiating rule " << ri << "\n";);
			rule_instance_info* info = alloc(rule_instance_info, get_subst_vect_free(ri, "s", m), solver, m);

			try {
				// create ground body
				expr_ref_vector body = m_subst.apply(ri->get_body(m_template_param_values, m_subst), info->m_rule_subst);
				pre_simplify(body);
				info->m_body.swap(body);

				// instantiate explicit arguments to head applications
				if (ri->get_decl()) {
					expr_ref_vector head_args = m_subst.apply(ri->get_explicit_args(), info->m_rule_subst);
					pre_simplify(head_args);
					vector<bool> known_args = known_exprs(head_args);
					info->m_head_explicit_args.swap(head_args);
					info->m_head_known_args.swap(known_args);
				}

				info->m_num_head_unknown_args = 0;
				for (unsigned i = 0; i < info->m_head_known_args.size(); ++i) {
					if (!info->m_head_known_args.get(i)) {
						++info->m_num_head_unknown_args;
					}
				}

				// instantiate explicit arguments to body applications
				for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
					CASSERT("predabst", ri->get_decl(i));
					expr_ref_vector body_args = m_subst.apply(ri->get_explicit_args(i), info->m_rule_subst);
					pre_simplify(body_args);
					vector<bool> known_args = known_exprs(body_args);
					info->m_body_explicit_args.push_back(body_args);
					info->m_body_known_args.push_back(known_args);
				}

				// create placeholders for body applications
				for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
					info->m_body_preds.push_back(expr_ref_vector(m));
				}

				if (m_fp_params.solver_per_rule()) {
					for (unsigned i = 0; i < info->m_body.size(); ++i) {
						solver->assert_expr(info->m_body.get(i));
					}
				}

				scoped_push _push1(*solver); // >>> unnecessary if solver_per_rule
				if (!m_fp_params.solver_per_rule()) {
					for (unsigned i = 0; i < info->m_body.size(); ++i) {
						solver->assert_expr(info->m_body.get(i));
					}
				}

				lbool result = check(solver);
				if (result == l_false) {
					// unsat body
					STRACE("predabst", tout << "Rule " << ri << " will always fail\n";);
					m_stats.m_num_rules_unsatisfiable++;
					info->m_unsat = true;
				}
				else {
					info->m_unsat = false;
				}

				return info;
			}
			catch (...) {
				dealloc(info);
				throw;
			}
		}

		void instantiate_rule_preds(rule_info* ri) {
			STRACE("predabst", tout << "Instantiating predicates for rule " << ri << "\n";);
			rule_instance_info* info = m_rule_instances[ri];

			scoped_push push(*solver_for(ri)); // >>> unnecessary if solver per rule
			if (!m_fp_params.solver_per_rule()) {
				for (unsigned i = 0; i < info->m_body.size(); ++i) {
					solver_for(ri)->assert_expr(info->m_body.get(i));
				}
			}

			// create instantiations for head applications
			symbol_info const* si = ri->get_decl();
			if (si) {
				expr_ref_vector head_args = m_subst.apply(ri->get_abstracted_args(), info->m_rule_subst);
				expr_ref_vector head_preds = app_inst_preds(si, head_args, info->m_head_preds.size());
				invert(head_preds);
				pre_simplify(head_preds);
				if (m_fp_params.convert_true_head_preds()) {
					maybe_make_true(head_preds, solver_for(ri));
				}
				if (m_fp_params.convert_false_head_preds()) {
					maybe_make_false(head_preds, solver_for(ri));
				}
				if (m_fp_params.solver_per_rule()) {
					assert_guarded_exprs(head_preds, solver_for(ri));
				}
				else {
					info->m_head_preds.append(head_preds);
					m_stats.m_num_head_predicates += head_preds.size();
				}
			}

			// create instantiations for body applications
			for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
				symbol_info const* si = ri->get_decl(i);
				CASSERT("predabst", si);
				expr_ref_vector body_args = m_subst.apply(ri->get_abstracted_args(i), info->m_rule_subst);
				expr_ref_vector body_preds = app_inst_preds(si, body_args, info->m_body_preds.get(i).size());
				pre_simplify(body_preds);
				if (m_fp_params.convert_true_body_preds()) {
					maybe_make_true(body_preds, solver_for(ri));
				}
				if (m_fp_params.convert_false_body_preds()) {
					maybe_make_false(body_preds, solver_for(ri));
				}
				if (m_fp_params.solver_per_rule()) {
					assert_guarded_exprs(body_preds, solver_for(ri));
				}
				else {
					info->m_body_preds.get(i).append(body_preds);
					m_stats.m_num_body_predicates += body_preds.size();
				}
			}
		}

		// instantiate each predicate by replacing its free variables with (grounded) arguments of gappl
		expr_ref_vector app_inst_preds(symbol_info const* si, expr_ref_vector const& args, unsigned num_pred_instances) {
			// instantiation maps preds variables to head arguments
			expr_ref_vector inst = m_subst.build(si->m_abstracted_vars, args);
			// preds instantiates to inst_preds
			return m_subst.apply(expr_ref_vector(m, si->m_preds.size() - num_pred_instances, si->m_preds.c_ptr() + num_pred_instances), inst);
		}

		void initialize_abs(rule_info const* ri) {
			cart_pred_abst_rule(ri);
		}

		void inference_step(node_info const* node) {
			// Find all rules whose body contains the func_decl of the new node.
			symbol_info const* si = node->m_symbol;
			vector<rule_info const*> const& rules = si->m_users;
			STRACE("predabst", tout << "Performing inference from node " << node << " using rules " << rules << "\n";);
			for (vector<rule_info const*>::const_iterator r_it = rules.begin(); r_it != rules.end(); ++r_it) {
				rule_info const* ri = *r_it;
				STRACE("predabst-cprod", tout << "Attempting to apply rule " << ri << "\n";);
				// Find all positions in the body of this rule at which the
				// func_decl appears.
				uint_set positions = get_rule_body_positions(ri, si);
				CASSERT("predabst", positions.num_elems() != 0);
				for (uint_set::iterator p_it = positions.begin(); p_it != positions.end(); ++p_it) {
					STRACE("predabst-cprod", tout << "Using this node in position " << *p_it << "\n";);
					// Try all possible combinations of nodes that can be used
					// with this rule, assuming that the new node is used at
					// this position.
					cart_pred_abst_rule(ri, *p_it, node);
				}
			}
		}

		uint_set get_rule_body_positions(rule_info const* ri, symbol_info const* si) {
			uint_set positions;
			for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
				if (ri->get_decl(i) == si) {
					positions.insert(i);
				}
			}
			return positions;
		}

		bool model_eval_true(model_ref const& modref, expr_ref const& cube) {
			expr_ref val(m);
			if (m_fp_params.summarize_cubes()) { // >>> and not summarize_via_iff?
				if (!modref->eval(cube, val)) {
					CASSERT("predabst", "Failed to evaluate!\n"); // >>>
					throw default_exception("failed to evaluate");
				}
				CASSERT("predabst", m.is_true(val) || m.is_false(val) || val == cube);
				return !m.is_false(val);
			}
			else {
				if (!modref->eval(cube, val, true)) {
					CASSERT("predabst", "Failed to evaluate!\n"); // >>>
					throw default_exception("failed to evaluate");
				}
				CASSERT("predabst", m.is_true(val) || m.is_false(val));
				return m.is_true(val);
			}
		}

		// This is implementing the "abstract inference rules" from Figure 2 of "synthesizing software verifiers from proof rules".
		// With no 3rd argument, rule Rinit is applied; otherwise rule Rstep is applied.
		void cart_pred_abst_rule(rule_info const* ri, unsigned fixed_pos = 0, node_info const* fixed_node = NULL) {
			rule_instance_info const* info = m_rule_instances[ri];
			CASSERT("predabst", (fixed_node == NULL) || (fixed_pos < ri->get_tail_size()));

			if (info->m_unsat) {
				STRACE("predabst", tout << "Skipping rule " << ri << " with unsatisfiable body\n";);
				return;
			}

			STRACE("predabst", {
				if (fixed_node == NULL) {
					tout << "Using rule " << ri << "\n";
				}
				else {
					tout << "Using rule " << ri << " with node " << fixed_node << " in position " << fixed_pos << "\n";
				}
			});

			// Build the sets of nodes for each position.
			vector<node_vector> all_nodes;
			unsigned all_combs = 1;
			for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
				node_vector pos_nodes;
				unsigned pos_nodes_size = 0;
				node_vector const& nodes = (i == fixed_pos) ? singleton_set(fixed_node) : m_max_reach_nodes[ri->get_decl(i)];
				for (node_vector::const_iterator it = nodes.begin(); it != nodes.end(); ++it) {
					node_info const* node = *it;
					if ((node->m_id > fixed_node->m_id) || ((i > fixed_pos) && (node->m_id == fixed_node->m_id))) {
						// Don't use any nodes newer than the fixed node; we'll have a chance to use newer nodes when they are taken off the worklist later.
						// Furthermore, don't use the fixed node further along that the fixed position; we'll have a chance to use it in both places when the fixed position advances.
						// Note that iterating over the max_reach_nodes set return nodes in ascending order, so we can bail out here.
						break;
					}

					bool skip = false;
					cube_t const& cube = node->m_cube;
					expr_ref_vector const& body_preds = info->m_body_preds[i];
					unsigned num_preds = body_preds.size();
					CASSERT("predabst", num_preds == cube.size());
					for (unsigned j = 0; j < num_preds; ++j) {
						if (cube[j]) {
							if (m_fp_params.skip_false_body_preds() && m.is_false(body_preds[j])) {
								// Skip parent nodes that are trivially inconsistent with this rule.
								skip = true;
								break;
							}
						}
					}
					if (!skip) {
						expr_ref_vector const& values = node->m_values;
						expr_ref_vector const& body_args = info->m_body_explicit_args[i];
						vector<bool> const& known_args = info->m_body_known_args[i];
						CASSERT("predabst", values.size() == body_args.size());
						for (unsigned j = 0; j < values.size(); ++j) {
							if (m_fp_params.skip_incorrect_body_values() && known_args.get(j) && (body_args.get(j) != values.get(j))) {
								// Skip parent nodes that are trivially inconsistent with this application.
								skip = true;
								break;
							}
						}
					}
					if (!skip) {
						pos_nodes.insert(node);
						++pos_nodes_size;
					}
				}
				all_nodes.push_back(pos_nodes);
				all_combs *= pos_nodes_size;
			}

			unsigned found_combs = 0;
			if (m_fp_params.bail_if_no_combinations() && (found_combs == all_combs)) {
				STRACE("predabst", tout << "Candidate node set (" << all_nodes << ") has empty product\n";);
				return;
			}

			// Build the sets of cubes for each position.
			vector<vector<expr_ref_vector>> all_cubes; // >>> I'm not sure vector<vector<...>> works correctly, since vector's copy-constructor copies its members using memcpy.
			for (unsigned i = 0; i < all_nodes.size(); ++i) {
				node_vector pos_nodes = all_nodes.get(i);
				vector<expr_ref_vector> pos_cubes;
				for (node_vector::iterator it = pos_nodes.begin(); it != pos_nodes.end(); ++it) {
					node_info const* node = *it;
					expr_ref_vector pos_cube(m);
					cube_t const& cube = node->m_cube;
					expr_ref_vector const& body_preds = info->m_body_preds[i];
					unsigned num_preds = body_preds.size();
					CASSERT("predabst", num_preds == cube.size());
					for (unsigned j = 0; j < num_preds; ++j) {
						if (cube[j]) {
							CASSERT("predabst", !(m_fp_params.skip_false_body_preds() && m.is_false(body_preds[j])));
							if (m_fp_params.skip_true_body_preds() && m.is_true(body_preds[j])) {
								continue;
							}
							pos_cube.push_back(body_preds[j]);
						}
					}
					expr_ref_vector const& values = node->m_values;
					expr_ref_vector const& body_args = info->m_body_explicit_args[i];
					vector<bool> const& known_args = info->m_body_known_args[i];
					CASSERT("predabst", values.size() == body_args.size());
					for (unsigned j = 0; j < values.size(); ++j) {
						CASSERT("predabst", !(m_fp_params.skip_incorrect_body_values() && known_args.get(j) && (body_args.get(j) != values.get(j))));
						if (m_fp_params.skip_correct_body_values() && (body_args.get(j) == values.get(j))) {
							continue;
						}
						pos_cube.push_back(m.mk_eq(body_args.get(j), values.get(j)));
					}
					pos_cubes.push_back(pos_cube);
				}
				all_cubes.push_back(pos_cubes);
			}

			STRACE("predabst", tout << "Using candidate node set (" << all_nodes << ") with cubes (" << all_cubes << ")\n";); // "cubes" here are not useful if they're cv's

			// This push is unnecessary if (solver_per_rule() && !use_allsat()).
			scoped_push _push1(*solver_for(ri));

			if (!m_fp_params.solver_per_rule()) {
				for (unsigned i = 0; i < info->m_body.size(); ++i) {
					solver_for(ri)->assert_expr(info->m_body[i]);
				}
			}

			expr_ref_vector head_es = info->m_head_preds;
			if (!m_fp_params.solver_per_rule()) {
				if (m_fp_params.use_head_assumptions()) {
					assert_guarded_exprs(head_es, solver_for(ri));
				}
			}

			// >>> move to query()
			if (m_fp_params.use_body_assumptions() && !m_fp_params.solver_per_rule() && !m_fp_params.summarize_cubes()) {
				STRACE("predabst", tout << "Can't use body assumptions without having guard variables to assume\n";);
				throw default_exception("can't use body assumptions without having guard variables to assume");
			}

			if (m_fp_params.summarize_cubes()) {
				for (unsigned i = 0; i < all_cubes.size(); ++i) {
					vector<expr_ref_vector>& pos_cubes = all_cubes[i];
					for (unsigned j = 0; j < pos_cubes.size(); ++j) {
						expr_ref_vector& pos_cube = pos_cubes.get(j);
						expr_ref_vector pos_cube2(m);
						expr_ref cube_guard_var(m.mk_fresh_const("cv", m.mk_bool_sort()), m);
						if (m_fp_params.summarize_cubes_using_iff()) {
							expr_ref to_assert(m.mk_iff(mk_conj(pos_cube), cube_guard_var), m);
							pre_simplify(to_assert);
							solver_for(ri)->assert_expr(to_assert);
						}
						else {
							for (unsigned j = 0; j < pos_cube.size(); ++j) {
								expr_ref to_assert(m.mk_or(m.mk_not(cube_guard_var), pos_cube.get(j)), m);
								solver_for(ri)->assert_expr(to_assert);
							}
						}
						pos_cube.reset();
						pos_cube.push_back(cube_guard_var);
					}
				}
			}

			if (m_fp_params.use_allsat()) {
				for (unsigned i = 0; i < all_cubes.size(); ++i) {
					vector<expr_ref_vector> const& pos_cubes = all_cubes[i];
					if (pos_cubes.size() == 1) {
						expr_ref_vector const& pos_cube = pos_cubes[0];
						for (unsigned k = 0; k < pos_cube.size(); ++k) {
							solver_for(ri)->assert_expr(pos_cube.get(k));
						}
					}
					else {
						expr_ref_vector pos_disjs(m);
						for (unsigned j = 0; j < pos_cubes.size(); ++j) {
							expr_ref_vector const& pos_cube = pos_cubes[j];
							pos_disjs.push_back(mk_conj(pos_cube));
						}
						expr_ref to_assert = mk_disj(pos_disjs);
						pre_simplify(to_assert);
						solver_for(ri)->assert_expr(to_assert);
					}
				}

				m_fparams.m_model = (all_combs > 1);

				while (check(solver_for(ri)) == l_true) {
					model_ref modref;
					if (all_combs > 1) {
						solver_for(ri)->get_model(modref);
					}

					// Build the sets of satisfiable nodes/cubes for each position.
					vector<node_vector> sat_nodes;
					vector<vector<expr_ref_vector>> sat_cubes;
					unsigned sat_combs = 1;
					for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
						node_vector sat_pos_nodes;
						vector<expr_ref_vector> sat_pos_cubes;
						node_vector const& pos_nodes = all_nodes[i];
						vector<expr_ref_vector> const& pos_cubes = all_cubes[i];
						unsigned j = 0;
						for (node_vector::const_iterator it = pos_nodes.begin(); it != pos_nodes.end(); ++it, ++j) {
							node_info const* node = *it;
							expr_ref cube(mk_conj(pos_cubes[j]), m);
							// No need to evaluate P with respect to the model when we know that the model already satisfies P.
							// >>> This optimization is probably not worth anything if the "cubes" here were guard_vars.
							if ((m_fp_params.skip_singleton_model_eval() && (pos_cubes.size() == 1)) || model_eval_true(modref, cube)) {
								sat_pos_nodes.insert(node);
								sat_pos_cubes.push_back(pos_cubes[j]);
							}
						}
						CASSERT("predabst", j == pos_cubes.size());
						sat_nodes.push_back(sat_pos_nodes);
						sat_cubes.push_back(sat_pos_cubes);
						sat_combs *= sat_pos_cubes.size();
					}

					STRACE("predabst", tout << "Found satisfiable node set (" << sat_nodes << ") with cubes (" << sat_cubes << ")\n";); // "cubes" here are not useful if they're cv's

					// Now take the Cartesian product.
					m_fparams.m_model = false;
					cart_pred_abst_rule(ri, head_es, all_cubes, sat_nodes, sat_cubes, true);
					m_fparams.m_model = (all_combs > 1);

					CASSERT("predabst", sat_combs > 0);
					found_combs += sat_combs;
					CASSERT("predabst", found_combs <= all_combs);
					if (m_fp_params.bail_if_all_combinations_sat() && (found_combs == all_combs)) {
						STRACE("predabst", tout << "All possible combinations were satisfiable\n";);
						break;
					}

					// Add a constraint to avoid visiting this solution again.
					expr_ref_vector conjs(m);
					for (unsigned i = 0; i < sat_cubes.size(); ++i) {
						vector<expr_ref_vector> const& sat_pos_cubes = sat_cubes[i];
						expr_ref_vector disjs(m);
						for (unsigned j = 0; j < sat_pos_cubes.size(); ++j) {
							disjs.push_back(mk_conj(sat_pos_cubes[j]));
						}
						conjs.push_back(mk_disj(disjs));
					}
					expr_ref to_assert = mk_not(mk_conj(conjs));
					STRACE("predabst", tout << "  " << to_assert << "\n";);
					pre_simplify(to_assert);
					solver_for(ri)->assert_expr(to_assert);
				}

				m_fparams.m_model = false;
			}
			else {
				cart_pred_abst_rule(ri, head_es, all_cubes, all_nodes, all_cubes, false);
			}
		}

		void cart_pred_abst_rule(rule_info const* ri, expr_ref_vector const& head_es, vector<vector<expr_ref_vector>> const& all_cubes, vector<node_vector> const& nodes, vector<vector<expr_ref_vector>> const& cubes, bool assume_sat) {
			vector<unsigned> positions = get_rule_position_ordering(cubes);
			node_vector chosen_nodes;
			expr_ref_vector assumptions(m);
			cart_pred_abst_rule(ri, head_es, all_cubes, nodes, cubes, positions, chosen_nodes, assumptions, assume_sat);
		}

		template<typename T>
		vector<unsigned> get_rule_position_ordering(vector<vector<T>> const& sizes) {
			std::vector<std::pair<unsigned, unsigned>> pos_counts;
			for (unsigned i = 0; i < sizes.size(); ++i) {
				unsigned n = sizes.get(i).size();
				STRACE("predabst-cprod", tout << "There are " << n << " option(s) for position " << i << "\n";);
				pos_counts.push_back(std::make_pair(n, i));
			}

			if (m_fp_params.order_cartprod_choices()) {
				std::stable_sort(pos_counts.begin(), pos_counts.end());
			}

			vector<unsigned> positions;
			for (unsigned i = 0; i < pos_counts.size(); ++i) {
				positions.push_back(pos_counts[i].second);
			}
			return positions;
		}

		node_vector reorder_nodes(node_vector const& nodes, vector<unsigned> const& pos_order) {
			CASSERT("predabst", nodes.size() == pos_order.size());
			node_vector reordered;
			reordered.reserve(pos_order.size());
			for (unsigned i = 0; i < pos_order.size(); ++i) {
				reordered[pos_order[i]] = nodes[i];
			}
			return reordered;
		}

		void reorder_output_nodes(std::ostream& out, node_vector const& nodes, vector<unsigned> const& pos_order) {
			CASSERT("predabst", nodes.size() <= pos_order.size());
			node_vector reordered;
			vector<bool> found;
			reordered.reserve(pos_order.size());
			found.reserve(pos_order.size(), false);
			for (unsigned i = 0; i < nodes.size(); ++i) {
				reordered[pos_order[i]] = nodes[i];
				found[pos_order[i]] = true;
			}
			for (unsigned i = 0; i < pos_order.size(); ++i) {
				if (i > 0) {
					out << ", ";
				}
				if (found[i]) {
					out << reordered[i];
				}
				else {
					out << "?";
				}
			}
		}

		static node_vector singleton_set(node_info const* node) {
			node_vector s;
			s.insert(node);
			return s;
		}

		void cart_pred_abst_rule(rule_info const* ri, expr_ref_vector const& head_es, vector<vector<expr_ref_vector>> const& all_cubes, vector<node_vector> const& nodes, vector<vector<expr_ref_vector>> const& cubes, vector<unsigned> const& positions, node_vector& chosen_nodes, expr_ref_vector& assumptions, bool assume_sat) {
			CASSERT("predabst", all_cubes.size() == ri->get_tail_size());
			CASSERT("predabst", nodes.size() == ri->get_tail_size());
			CASSERT("predabst", cubes.size() == ri->get_tail_size());
			CASSERT("predabst", positions.size() == ri->get_tail_size());
			CASSERT("predabst", chosen_nodes.size() <= ri->get_tail_size());

			if (chosen_nodes.size() < positions.size()) {
				unsigned i = positions[chosen_nodes.size()];
				node_vector const& pos_nodes = nodes[i];
				vector<expr_ref_vector> const& pos_cubes = cubes[i];
				unsigned j = 0;
				for (node_vector::const_iterator it = pos_nodes.begin(); it != pos_nodes.end(); ++it, ++j) {
					node_info const* chosen_node = *it;
					chosen_nodes.push_back(chosen_node);
					expr_ref_vector const& pos_cube = pos_cubes[j];
					if ((assume_sat && (all_cubes[i].size() == 1)) || (pos_cube.size() == 0)) {
						// No need to assert P again when we have already done so.
						cart_pred_abst_rule(ri, head_es, all_cubes, nodes, cubes, positions, chosen_nodes, assumptions, assume_sat);
					}
					else {
						if (m_fp_params.use_body_assumptions()) {
							assumptions.append(pos_cube);
						}
						else {
							solver_for(ri)->push();
							for (unsigned k = 0; k < pos_cube.size(); ++k) {
								solver_for(ri)->assert_expr(pos_cube.get(k));
							}
						}

						bool sat = true;
						if (!assume_sat) {
							lbool result = check(solver_for(ri), assumptions.size(), assumptions.c_ptr());
							if (result == l_false) {
								m_stats.m_num_body_checks_unsat++;
							}
							else {
								m_stats.m_num_body_checks_sat++;
							}
							sat = (result != l_false);
						}

						if (!sat) {
							// unsat body
							STRACE("predabst", tout << "Applying rule " << ri << " to nodes ("; reorder_output_nodes(tout, chosen_nodes, positions); tout << ") failed\n";);
						}
						else {
							cart_pred_abst_rule(ri, head_es, all_cubes, nodes, cubes, positions, chosen_nodes, assumptions, assume_sat);
						}
						if (m_fp_params.use_body_assumptions()) {
							assumptions.resize(assumptions.size() - pos_cube.size());
						}
						else {
							solver_for(ri)->pop(1);
						}
					}
					chosen_nodes.pop_back();
				}
				CASSERT("predabst", j == pos_cubes.size());
			}
			else {
				CASSERT("predabst", check(solver_for(ri), assumptions.size(), assumptions.c_ptr()) != l_false);

				// collect abstract cube and explicit values
				cube_t cube = cart_pred_abst_cube(ri, head_es, assumptions);
				expr_ref_vector values = cart_pred_abst_values(ri, assumptions);
				STRACE("predabst", tout << "Applying rule " << ri << " to nodes ("; reorder_output_nodes(tout, chosen_nodes, positions); tout << ") gives cube [" << cube << "] and values (" << values << ")\n";);

				// add and check the node
				node_info const* node = add_node(ri, cube, values, reorder_nodes(chosen_nodes, positions));
				if (node) {
					check_node_property(node);
				}
			}
		}

		cube_t cart_pred_abst_cube(rule_info const* ri, expr_ref_vector const& es, expr_ref_vector& assumptions) {
			rule_instance_info const* info = m_rule_instances[ri];
			unsigned num_preds = es.size();
			CASSERT("predabst", (!ri->get_decl() && (num_preds == 0)) || (num_preds == ri->get_decl()->m_preds.size()));
			cube_t cube;
			cube.resize(num_preds);
			for (unsigned i = 0; i < num_preds; ++i) {
				if (m_fp_params.skip_false_head_preds() && m.is_false(es.get(i))) {
					cube[i] = true;
				}
				else if (m_fp_params.skip_true_head_preds() && m.is_true(es.get(i))) {
					cube[i] = false;
				}
				else {
					if (m_fp_params.use_head_assumptions()) {
						assumptions.push_back(es.get(i));
					}
					else {
						solver_for(ri)->push();
						solver_for(ri)->assert_expr(es.get(i));
					}
					lbool result = check(solver_for(ri), assumptions.size(), assumptions.c_ptr());
					cube[i] = (result == l_false);
					if (result == l_false) {
						m_stats.m_num_head_checks_unsat++;
					}
					else {
						m_stats.m_num_head_checks_sat++;
					}
					if (m_fp_params.use_head_assumptions()) {
						assumptions.pop_back();
					}
					else {
						solver_for(ri)->pop(1);
					}
				}
			}
			return cube;
		}

		expr_ref_vector cart_pred_abst_values(rule_info const* ri, expr_ref_vector const& assumptions) {
			rule_instance_info const* info = m_rule_instances[ri];
			expr_ref_vector values(m);
			if (info->m_head_explicit_args.size() == 0) {
				// nothing to do
			}
			else if (m_fp_params.skip_known_head_values() && (info->m_num_head_unknown_args == 0)) {
				values.append(info->m_head_explicit_args);
			}
			else {
				bool old_model = m_fparams.m_model;
				m_fparams.m_model = true;
				lbool result = check(solver_for(ri), assumptions.size(), assumptions.c_ptr());
				CASSERT("predabst", result == l_true);
				m_fparams.m_model = old_model;
				model_ref modref;
				solver_for(ri)->get_model(modref);
				CASSERT("predabst", modref);
				model_evaluator ev(*modref);
				ev.set_model_completion(true);
				for (unsigned i = 0; i < info->m_head_explicit_args.size(); ++i) {
					if (m_fp_params.skip_known_head_values() && info->m_head_known_args.get(i)) {
						values.push_back(info->m_head_explicit_args.get(i));
					}
					else {
						expr_ref val(m);
						try {
							ev(info->m_head_explicit_args.get(i), val);
						}
						catch (model_evaluator_exception& ex) {
							(void)ex;
							STRACE("predabst", tout << "Failed to evaluate: " << ex.msg() << "\n";); // >>>
							throw default_exception("failed to evaluate");
						}
						values.push_back(val);
						m_stats.m_num_head_evals++;
					}
				}
			}
#ifdef Z3DEBUG
			// Check that these explicit values are uniquely determined.  This
			// check may fail if some arguments were incorrectly marked as
			// explicit.
			scoped_push _push(*solver_for(ri));
			expr_ref_vector es(m);
			for (unsigned i = 0; i < info->m_head_explicit_args.size(); ++i) {
				if (!info->m_head_known_args.get(i)) {
					es.push_back(m.mk_eq(info->m_head_explicit_args.get(i), values.get(i)));
				}
			}
			expr_ref to_assert(m.mk_not(mk_conj(es)), m);
			pre_simplify(to_assert);
			solver_for(ri)->assert_expr(to_assert);
			lbool result = check(solver_for(ri), assumptions.size(), assumptions.c_ptr());
			if (result == l_true) {
				STRACE("predabst", tout << "Error: values of explicit arguments were not uniquely determined\n";);
				throw default_exception("values of explicit arguments for " + ri->get_decl()->m_fdecl->get_name().str() + " were not uniquely determined");
			}
#endif
			return values;
		}

		void check_node_property(node_info const* node) {
			if (!node->m_symbol) {
				STRACE("predabst", tout << "Reached query symbol\n";);
				throw acr_error(node, reached_query);
			}
			if (node->m_symbol->m_is_dwf) {
				if (!is_well_founded(node)) {
					STRACE("predabst", tout << "Formula is not well-founded\n";);
					throw acr_error(node, not_dwf);
				}
				m_stats.m_num_well_founded_nodes++;
			}
		}

		bool is_well_founded(node_info const* node) {
			symbol_info const* si = node->m_symbol;
			CASSERT("predabst", si->m_is_dwf);

			CASSERT("predabst", node->m_values.size() % 2 == 0);
			unsigned n = node->m_values.size() / 2;
			for (unsigned i = 0; i < n; ++i) {
				if (node->m_values[i] != node->m_values[i + n]) {
					return true;
				}
			}

			expr_ref expr = cube_to_formula(node->m_cube, si->m_preds);
			expr_ref_vector args = si->get_fresh_args("s");
			expr_ref to_rank = m_subst.apply(expr, m_subst.build(si->m_abstracted_vars, args));

			return well_founded(args, to_rank, NULL, NULL);
		}

		node_info const* add_node(rule_info const* ri, cube_t const& cube, expr_ref_vector const& values, node_vector const& nodes = node_vector()) {
			CASSERT("predabst", cube.size() == m_rule_instances[ri]->m_head_preds.size());
			CASSERT("predabst", values.size() == m_rule_instances[ri]->m_head_explicit_args.size());
			m_stats.m_num_nodes_discovered++;
			symbol_info const* si = ri->get_decl();
			if (si) {
				// first fixpoint check combined with maximality maintainance
				node_vector old_lt_nodes;
				for (node_vector::const_iterator it = m_max_reach_nodes[si].begin(); it != m_max_reach_nodes[si].end(); ++it) {
					if (!vector_equals(values, (*it)->m_values)) {
						continue;
					}
					cube_t const& old_cube = (*it)->m_cube;
					// if cube implies existing cube then nothing to add
					if (cube_leq(cube, old_cube)) {
						STRACE("predabst", tout << "New node is subsumed by node " << *it << " with cube [" << old_cube << "]\n";);
						CASSERT("predabst", old_lt_nodes.empty());
						m_stats.m_num_nodes_suppressed++;
						return NULL;
					}
					// stronger old cubes will not be considered maximal
					if (cube_leq(old_cube, cube)) {
						STRACE("predabst", tout << "New node subsumes node " << *it << " with cube [" << old_cube << "]\n";);
						old_lt_nodes.push_back(*it);
					}
				}
				// (no???) fixpoint reached since didn't return
				// remove subsumed maximal nodes
				for (node_vector::const_iterator it = old_lt_nodes.begin(); it != old_lt_nodes.end(); ++it) {
					m_max_reach_nodes[si].erase(*it);
					m_stats.m_num_frontier_nodes_removed++;
					if (m_node_worklist.contains(*it)) {
						m_node_worklist.erase(*it); // removing non-existent element is ok
						m_stats.m_num_nodes_discarded++;
					}
				}
			}
			// no fixpoint reached hence create new node
			m_nodes.push_back(alloc(node_info, m_nodes.size(), si, cube, values, ri, nodes));
			node_info const* node = m_nodes.back();
			if (si) {
				m_max_reach_nodes[si].insert(node);
				m_stats.m_num_frontier_nodes_added++;
			}
			m_node_worklist.insert(node);
			m_stats.m_num_nodes_enqueued++;
			STRACE("predabst", tout << "Added node " << node << " for " << si << "\n";);
			return node;
		}

		expr_ref node_to_formula(node_info const* node) const {
			expr_ref_vector es(m);
			expr_ref_vector const& values = node->m_values;
			var_ref_vector const& args = node->m_symbol->m_explicit_vars;
			CASSERT("predabst", values.size() == args.size());
			for (unsigned i = 0; i < values.size(); ++i) {
				es.push_back(m.mk_eq(args.get(i), values.get(i)));
			}
			cube_t const& cube = node->m_cube;
			expr_ref_vector const& preds = node->m_symbol->m_preds;
			CASSERT("predabst", cube.size() == preds.size());
			for (unsigned i = 0; i < cube.size(); ++i) {
				if (cube[i]) {
					es.push_back(preds[i]);
				}
			}
			return mk_conj(es);
		}

		void print_instantiated_rules(std::ostream& out) const {
			out << "=====================================\n";
			out << "  Instantiated rules:" << std::endl;
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				rule_info const* ri = m_rules[i];
				rule_instance_info const* info = m_rule_instances[ri];
				out << "    " << i << ":" << std::endl;
				out << "      head preds (" << ri->get_decl() << "): " << info->m_head_preds << "\n";
				out << "      head explicit args (" << ri->get_decl() << "): " << info->m_head_explicit_args << "\n";
				CASSERT("predabst", ri->get_tail_size() == info->m_body_preds.size());
				CASSERT("predabst", ri->get_tail_size() == info->m_body_explicit_args.size());
				for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
					out << "      body preds " << i << " (" << ri->get_decl(i) << "): " << info->m_body_preds[i] << "\n";
					out << "      body explicit args " << i << " (" << ri->get_decl(i) << "): " << info->m_body_explicit_args[i] << "\n";
				}
				out << "      body: " << mk_conj(info->m_body) << "\n";
			}
			out << "=====================================\n";
		}

		void print_inference_state(std::ostream& out, unsigned refine_count, unsigned infer_count) const {
			out << "=====================================\n";
			out << "State before inference step " << refine_count << "." << infer_count << ":\n";
			out << "  Nodes:" << std::endl;
			for (unsigned i = 0; i < m_nodes.size(); ++i) {
				node_info const* node = m_nodes[i];
				out << "    " << i << ": rule " << node->m_parent_rule
					<< " applied to nodes (" << node->m_parent_nodes
					<< ") giving cube [" << node->m_cube
					<< "] and values (" << node->m_values
					<< ") for " << node->m_symbol
					<< std::endl;
			}
			out << "  Max reached nodes:" << std::endl;
			for (obj_map<symbol_info const, node_vector>::iterator it = m_max_reach_nodes.begin(); it != m_max_reach_nodes.end(); ++it) {
				symbol_info const* si = it->m_key;
				out << "    " << si << ": "	<< it->m_value << std::endl;
			}
			out << "  Worklist: " << m_node_worklist << std::endl;
			out << "=====================================\n";
		}
	};

	predabst_core::predabst_core(vector<symbol_info*> const& symbols, vector<rule_info*> const& rules, expr_ref_vector const& template_param_values, fixedpoint_params const& fp_params, ast_manager& m) :
		m_imp(alloc(imp, symbols, rules, template_param_values, fp_params, m)) {
	}
	
	predabst_core::~predabst_core() {
		dealloc(m_imp);
	}

	bool predabst_core::find_solution(unsigned refine_count) {
		return m_imp->find_solution(refine_count);
	}

	expr_ref predabst_core::get_model(symbol_info const* si) const {
		return m_imp->get_model(si);
	}

	counterexample_kind predabst_core::get_counterexample_kind() const {
		return m_imp->get_counterexample_kind();
	}

	node_info const* predabst_core::get_counterexample() const {
		return m_imp->get_counterexample();
	}
}
