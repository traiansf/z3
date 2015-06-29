/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

	predabst_rule.cpp

Abstract:

	Bounded PREDABST (symbolic simulation using Z3) rule.

Author:

	Created by James Lingard (jchl) 2015-06-22.

Revision History:

--*/
#include "predabst_util.h"
#include "predabst_rule.h"

namespace datalog {
	expr_ref_vector rule_info::get_abstracted_args() const {
		if (get_decl()) {
			expr_ref_vector args(m);
			for (unsigned i = 0; i < get_decl()->m_explicit_args.size(); ++i) {
				if (!get_decl()->m_explicit_args.get(i)) {
					args.push_back(get_head()->get_arg(i));
				}
			}
			return args;
		}
		else {
			return expr_ref_vector(m);
		}
	}

	expr_ref_vector rule_info::get_abstracted_args(unsigned i) const {
		CASSERT("predabst", get_decl(i));
		expr_ref_vector args(m);
		for (unsigned j = 0; j < get_decl(i)->m_explicit_args.size(); ++j) {
			if (!get_decl(i)->m_explicit_args.get(j)) {
				args.push_back(get_tail(i)->get_arg(j));
			}
		}
		return args;
	}

	expr_ref_vector rule_info::get_explicit_args() const {
		if (get_decl()) {
			expr_ref_vector args(m);
			for (unsigned i = 0; i < get_decl()->m_explicit_args.size(); ++i) {
				if (get_decl()->m_explicit_args.get(i)) {
					args.push_back(get_head()->get_arg(i));
				}
			}
			return args;
		}
		else {
			return expr_ref_vector(m);
		}
	}

	expr_ref_vector rule_info::get_explicit_args(unsigned i) const {
		CASSERT("predabst", get_decl(i));
		expr_ref_vector args(m);
		for (unsigned j = 0; j < get_decl(i)->m_explicit_args.size(); ++j) {
			if (get_decl(i)->m_explicit_args.get(j)) {
				args.push_back(get_tail(i)->get_arg(j));
			}
		}
		return args;
	}

	used_vars rule_info::get_used_vars() const {
		return ::get_used_vars(m_rule);
	}
}
