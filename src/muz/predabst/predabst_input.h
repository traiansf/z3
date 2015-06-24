/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

	predabst_input.h

Abstract:

	Predabst input processing.

Author:

	James Lingard (jchl) 2015-02-05.

Revision History:

--*/
#ifndef _PREDABST_INPUT_H_
#define _PREDABST_INPUT_H_

#include "ast.h"
#include "fixedpoint_params.hpp"

namespace datalog {
	struct predabst_input {
		vector<symbol_info*>                m_symbols;
		vector<template_info*>              m_templates;
		vector<rule_info*>                  m_rules;
		expr_ref                            m_template_extras;
		expr_ref_vector                     m_template_params;

		predabst_input(ast_manager& m) :
			m_template_extras(m),
			m_template_params(m) {
		}

		~predabst_input() {
			for (unsigned i = 0; i < m_symbols.size(); ++i) {
				dealloc(m_symbols[i]);
			}
			for (unsigned i = 0; i < m_templates.size(); ++i) {
				dealloc(m_templates[i]);
			}
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				dealloc(m_rules[i]);
			}
		}

		struct stats {
			stats() { reset(); }
			void reset() { memset(this, 0, sizeof(*this)); }

			unsigned m_num_predicate_symbols;
			unsigned m_num_predicate_symbol_arguments;
			unsigned m_num_explicit_arguments;
			unsigned m_num_named_arguments;
			unsigned m_num_template_params;
			unsigned m_num_templates;
			unsigned m_num_initial_predicates;
			unsigned m_num_rules;

			void update(statistics& st) {
#define UPDATE_STAT(NAME) st.update(#NAME, m_ ## NAME)
				UPDATE_STAT(num_predicate_symbols);
				UPDATE_STAT(num_predicate_symbol_arguments);
				UPDATE_STAT(num_explicit_arguments);
				UPDATE_STAT(num_named_arguments);
				UPDATE_STAT(num_template_params);
				UPDATE_STAT(num_templates);
				UPDATE_STAT(num_initial_predicates);
				UPDATE_STAT(num_rules);
			}
		};
	};

	predabst_input* make_predabst_input(rule_set& rules, ast_manager& m, subst_util& subst, expr_ref_vector const& template_param_values, fixedpoint_params const& fp_params);
}

#endif /* _PREDABST_INPUT_H */
