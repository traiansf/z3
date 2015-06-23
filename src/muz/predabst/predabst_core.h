/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

predabst_core.h

Abstract:

Predicate abstraction core.

Author:

James Lingard (jchl) 2015-06-22

Revision History:

--*/
#ifndef _PREDABST_CORE_H_
#define _PREDABST_CORE_H_

#include "predabst_rule.h"
#include "ast.h"
#include "fixedpoint_params.hpp"

namespace datalog {
	typedef vector<bool> cube_t;

	struct node_info;
	typedef vector<node_info const*> node_vector;

	struct node_info {
		unsigned              const m_id;
		func_decl_info const* const m_fdecl_info;
		cube_t                const m_cube;
		expr_ref_vector       const m_explicit_values;
		rule_info const*      const m_parent_rule;
		node_vector           const m_parent_nodes;
		node_info(unsigned id, func_decl_info const* fdecl_info, cube_t const& cube, expr_ref_vector const& explicit_values, rule_info const* parent_rule, node_vector const& parent_nodes) :
			m_id(id),
			m_fdecl_info(fdecl_info),
			m_cube(cube),
			m_explicit_values(explicit_values),
			m_parent_rule(parent_rule),
			m_parent_nodes(parent_nodes) {}
		friend std::ostream& operator<<(std::ostream& out, node_info const* node) {
			out << node->m_id;
			return out;
		}
	};

	typedef enum { reached_query, not_wf } acr_error_kind; // >>> rename

	class predabst_core {
		class imp;
		imp* m_imp;

	public:
		struct stats {
			stats() { reset(); }
			void reset() { memset(this, 0, sizeof(*this)); }
			// Statistics about rule pre-processing.  Note that these are
			// cumulative over all template refinement iterations.
			unsigned m_num_head_predicates;
			unsigned m_num_body_predicates;
			unsigned m_num_true_predicates;
			unsigned m_num_false_predicates;
			unsigned m_num_known_explicit_arguments;
			unsigned m_num_rules_unsatisfiable;

			// Statistics about find_solution.  Note that these are cumulative
			// over all refinement iterations.
			unsigned m_num_nodes_discovered;
			unsigned m_num_nodes_suppressed; // discovered but not enqueued, because it implies an existing node
			unsigned m_num_nodes_enqueued;
			unsigned m_num_nodes_discarded; // enqueued but not dequeued, because it implies a subsequent node
			unsigned m_num_nodes_dequeued;
			unsigned m_num_frontier_nodes_added;
			unsigned m_num_frontier_nodes_removed;
			unsigned m_num_body_checks_sat;
			unsigned m_num_body_checks_unsat;
			unsigned m_num_head_checks_sat;
			unsigned m_num_head_checks_unsat;
			unsigned m_num_head_evals;
			unsigned m_num_well_founded_nodes;

			void update(statistics& st) {
#define UPDATE_STAT(NAME) st.update(#NAME, m_ ## NAME)
				UPDATE_STAT(num_head_predicates);
				UPDATE_STAT(num_body_predicates);
				UPDATE_STAT(num_true_predicates);
				UPDATE_STAT(num_false_predicates);
				UPDATE_STAT(num_known_explicit_arguments);
				UPDATE_STAT(num_rules_unsatisfiable);
				UPDATE_STAT(num_nodes_discovered);
				UPDATE_STAT(num_nodes_suppressed);
				UPDATE_STAT(num_nodes_enqueued);
				UPDATE_STAT(num_nodes_discarded);
				UPDATE_STAT(num_nodes_dequeued);
				UPDATE_STAT(num_frontier_nodes_added);
				UPDATE_STAT(num_frontier_nodes_removed);
				UPDATE_STAT(num_body_checks_sat);
				UPDATE_STAT(num_body_checks_unsat);
				UPDATE_STAT(num_head_checks_sat);
				UPDATE_STAT(num_head_checks_unsat);
				UPDATE_STAT(num_head_evals);
				UPDATE_STAT(num_well_founded_nodes);
			}
		};

		predabst_core(vector<func_decl_info*> const& func_decls, vector<rule_info*> const& rules, fixedpoint_params const& fp_params, ast_manager& m);
		~predabst_core();
		bool find_solution(unsigned refine_count);
		expr_ref get_model(func_decl_info const* fi) const;
		acr_error_kind get_counterexample_kind() const;
		node_info const* get_counterexample() const;
	};
};

#endif /* _PREDABST_CORE_H_ */
