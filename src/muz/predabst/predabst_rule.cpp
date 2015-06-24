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
				args.push_back(get_symbol_tail(i)->get_arg(j));
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
				args.push_back(get_symbol_tail(i)->get_arg(j));
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
		// The following is a clone of m_rule->get_used_vars(&used), which is unfortunately inaccessible.
		used_vars used;
		used.process(m_rule->get_head());
		for (unsigned i = 0; i < m_rule->get_tail_size(); ++i) {
			used.process(m_rule->get_tail(i));
		}
		return used;
	}

	rule_info* make_rule_info(unsigned id, rule* r, obj_map<func_decl, symbol_info*> const& func_decl2symbol, obj_map<func_decl, template_info*> const& func_decl2template, ast_manager& m) {
		symbol_info* head_symbol = NULL;
		if (func_decl2symbol.contains(r->get_decl())) {
			head_symbol = func_decl2symbol[r->get_decl()];
		}
		template_info* head_template = NULL;
		if (func_decl2template.contains(r->get_decl())) {
			head_template = func_decl2template[r->get_decl()];		
		}

		vector<symbol_info*> tail_symbols;
		vector<template_info*> tail_templates;
		vector<unsigned> symbol_pos;
		vector<unsigned> template_pos;
		for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
			if (func_decl2symbol.contains(r->get_decl(j))) {
				tail_symbols.push_back(func_decl2symbol[r->get_decl(j)]);
				symbol_pos.push_back(j);
			}
			if (func_decl2template.contains(r->get_decl(j))) {
				tail_templates.push_back(func_decl2template[r->get_decl(j)]);
				template_pos.push_back(j);
			}
		}

		return alloc(rule_info, id, r, head_symbol, head_template, tail_symbols, tail_templates, symbol_pos, template_pos, m);
	}
}
