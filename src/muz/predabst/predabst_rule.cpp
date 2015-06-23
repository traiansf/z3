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
	expr_ref_vector rule_info::get_non_explicit_args() const {
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
	expr_ref_vector rule_info::get_non_explicit_args(unsigned i) const {
		CASSERT("predabst", get_decl(i));
		expr_ref_vector args(m);
		for (unsigned j = 0; j < get_decl(i)->m_explicit_args.size(); ++j) {
			if (!get_decl(i)->m_explicit_args.get(j)) {
				args.push_back(get_uninterp_tail(i)->get_arg(j));
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
				args.push_back(get_uninterp_tail(i)->get_arg(j));
			}
		}
		return args;
	}
	expr_ref_vector rule_info::get_body(bool substitute_template_params) const {
		unsigned usz = m_rule->get_uninterpreted_tail_size();
		unsigned tsz = m_rule->get_tail_size();
		expr_ref_vector body = expr_ref_vector(m, tsz - usz, m_rule->get_expr_tail() + usz);
		if (m_head_template) {
			expr_ref_vector temp_body = m_head_template->get_body(get_head()->get_args(), substitute_template_params);
			body.push_back(mk_not(mk_conj(temp_body)));
		}
		for (unsigned i = 0; i < m_tail_templates.size(); ++i) {
			expr_ref_vector temp_body = m_tail_templates[i]->get_body(get_template_tail(i)->get_args(), substitute_template_params);
			body.append(temp_body);
		}
		return body;
	}
	used_vars rule_info::get_used_vars() const {
		used_vars used;
		// The following is a clone of m_rule->get_used_vars(&used), which is unfortunately inaccessible.
		used.process(m_rule->get_head());
		for (unsigned i = 0; i < m_rule->get_tail_size(); ++i) {
			used.process(m_rule->get_tail(i));
		}
		return used;
	}

	// Returns a substitution vector mapping each variable used in r to a
	// fresh constant.
	static expr_ref_vector get_subst_vect_free(rule* r, char const* prefix, ast_manager& m) {
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
				rule_subst[i] = m.mk_fresh_const(prefix, s);
			}
		}

		return rule_subst;
	}

	rule_info* make_rule_info(unsigned id, rule* r, obj_map<func_decl, func_decl_info*> const& func_decl2info, ast_manager& m, subst_util& subst) {
		func_decl_info* head_func_decl = NULL;
		template_info* head_temp = NULL;
		if (func_decl2info.contains(r->get_decl())) {
			func_decl_info* fi = func_decl2info[r->get_decl()];
			if (fi->m_template) {
				head_temp = fi->m_template;
			}
			else {
				head_func_decl = fi;
			}
		}

		vector<func_decl_info*> tail_func_decls;
		vector<template_info*> tail_temps;
		vector<unsigned> uninterp_pos;
		vector<unsigned> temp_pos;
		for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
			CASSERT("predabst", func_decl2info.contains(r->get_decl(j)));
			func_decl_info* fi = func_decl2info[r->get_decl(j)];
			if (fi->m_template) {
				tail_temps.push_back(fi->m_template);
				temp_pos.push_back(j);
			}
			else {
				tail_func_decls.push_back(fi);
				uninterp_pos.push_back(j);
			}
		}

		return alloc(rule_info, id, r, head_func_decl, tail_func_decls, uninterp_pos, head_temp, tail_temps, temp_pos, get_subst_vect_free(r, "c", m), m, subst);
	}
}
