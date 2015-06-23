/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

predabst_rule.h

Abstract:

Predicate abstraction rule.

Author:

James Lingard (jchl) 2015-06-22

Revision History:

--*/
#ifndef _PREDABST_RULE_H_
#define _PREDABST_RULE_H_

#include "ast.h"
#include "dl_rule.h"
#include "var_subst.h"

namespace datalog {
	class subst_util {
		ast_manager& m;
		var_subst    m_var_subst;

	public:
		subst_util(ast_manager& m) :
			m(m),
			m_var_subst(m, false) {}

		// Apply a substitution vector to an expression, returning the result.
		expr_ref apply(expr* expr, expr_ref_vector const& subst) {
			expr_ref expr2(m);
			m_var_subst(expr, subst.size(), subst.c_ptr(), expr2);
			return expr2;
		}

		// Apply a substitution vector to an application expression, returning the result.
		app_ref apply(app* app, expr_ref_vector const& subst) {
			expr_ref expr2(m);
			m_var_subst(app, subst.size(), subst.c_ptr(), expr2);
			return app_ref(to_app(expr2), m);
		}

		// Apply a substitution vector to each expression in a vector of
		// expressions, returning the result.
		expr_ref_vector apply(expr_ref_vector const& exprs, expr_ref_vector const& subst) {
			expr_ref_vector exprs2(m);
			exprs2.reserve(exprs.size());
			for (unsigned i = 0; i < exprs.size(); ++i) {
				exprs2[i] = apply(exprs[i], subst);
			}
			return exprs2;
		}

		// Returns a substitution vector that maps each variable in vars to the
		// corresponding expression in exprs.
		expr_ref_vector build(unsigned n, var* const* vars, expr* const* exprs) {
			expr_ref_vector inst(m);
			inst.reserve(n); // note that this is not necessarily the final size of inst
			for (unsigned i = 0; i < n; ++i) {
				unsigned idx = vars[i]->get_idx();
				inst.reserve(idx + 1);
				CASSERT("predabst", !inst.get(idx));
				inst[idx] = exprs[i];
			}
			return inst;
		}

		expr_ref_vector build(var* const* vars, expr_ref_vector const& exprs) {
			return build(exprs.size(), vars, exprs.c_ptr());
		}

		expr_ref_vector build(var_ref_vector const& vars, expr* const* exprs) {
			return build(vars.size(), vars.c_ptr(), exprs);
		}

		expr_ref_vector build(var_ref_vector const& vars, expr_ref_vector const& exprs) {
			CASSERT("predabst", vars.size() == exprs.size());
			return build(vars.size(), vars.c_ptr(), exprs.c_ptr());
		}

		expr_ref_vector build(var_ref_vector const& vars, var_ref_vector const& exprs) {
			CASSERT("predabst", vars.size() == exprs.size());
			return build(vars.size(), vars.c_ptr(), (expr* const*)exprs.c_ptr());
		}
	};

	struct rule_info;
	typedef vector<rule_info const*> rule_info_vector;

	struct template_info {
	public:
		var_ref_vector         const m_vars;
		expr_ref_vector        const m_body;
	private:
		expr_ref_vector const& m_template_params;
		expr_ref_vector const& m_template_param_values;
		subst_util&            m_subst;

	public:
		template_info(var_ref_vector const& vars, expr_ref_vector const& body, expr_ref_vector const& template_params, expr_ref_vector const& template_param_values, subst_util& subst) :
			m_vars(vars),
			m_body(body),
			m_template_params(template_params),
			m_template_param_values(template_param_values),
			m_subst(subst) {
		}
		expr_ref_vector get_body(expr* const* args, bool substitute_template_params = true) const {
			expr_ref_vector temp_args(m_vars.m(), m_vars.size() - m_template_params.size(), args);
			expr_ref_vector const& temp_params = substitute_template_params ? m_template_param_values : m_template_params;
			return m_subst.apply(m_body, m_subst.build(m_vars, vector_concat(temp_args, temp_params)));
		}
		expr_ref_vector get_body(var* const* args, bool substitute_template_params = true) const {
			return get_body((expr* const*)args, substitute_template_params);
		}
	};

	struct func_decl_info {
		func_decl*           const m_fdecl;
		var_ref_vector       const m_vars;
		expr_ref_vector      m_preds;
		func_decl_ref_vector m_var_names;
		vector<bool>         m_explicit_args;
		var_ref_vector       m_explicit_vars;
		var_ref_vector       m_non_explicit_vars;
		rule_info_vector     m_users;
		bool                 const m_is_dwf_predicate;
		template_info*       m_template;
		func_decl_info(func_decl* fdecl, var_ref_vector const& vars, bool is_dwf_predicate) :
			m_fdecl(fdecl),
			m_vars(vars),
			m_preds(vars.m()),
			m_var_names(vars.m()),
			m_explicit_vars(vars.m()),
			m_non_explicit_vars(vars.m()),
			m_is_dwf_predicate(is_dwf_predicate),
			m_template(NULL) {
			m_var_names.reserve(vars.size());
			m_explicit_args.reserve(vars.size());
		}
		expr_ref_vector get_fresh_args(char const* prefix) const {
			ast_manager& m = m_vars.m();
			expr_ref_vector args = get_arg_fresh_consts(m_fdecl, prefix, m);
			expr_ref_vector non_explicit_args(m);
			for (unsigned i = 0; i < m_explicit_args.size(); ++i) {
				if (!m_explicit_args.get(i)) {
					non_explicit_args.push_back(args.get(i));
				}
			}
			return non_explicit_args;
		}
		friend std::ostream& operator<<(std::ostream& out, func_decl_info const* fi) {
			if (fi) {
				out << fi->m_fdecl->get_name() << "/" << fi->m_fdecl->get_arity();
			}
			else {
				out << "<query>";
			}
			return out;
		}
		unsigned hash() const {
			return m_fdecl->hash();
		}
	};

	struct rule_info {
		unsigned                const m_id;
		rule*                   const m_rule;
	private:
		func_decl_info*         const m_head_func_decl;
		vector<func_decl_info*> const m_tail_func_decls;
		vector<unsigned>        const m_uninterp_pos;
		template_info*          const m_head_template;
		vector<template_info*>  const m_tail_templates;
		vector<unsigned>        const m_template_pos;
	public:
		expr_ref_vector         const m_rule_subst;
		ast_manager&            m;
		mutable subst_util&     m_subst;
		rule_info(unsigned id, rule* r, func_decl_info* head_func_decl, vector<func_decl_info*> const& tail_func_decls, vector<unsigned> const& uninterp_pos, template_info* head_temp, vector<template_info*> const& tail_temps, vector<unsigned> const& temp_pos, expr_ref_vector const& rule_subst, ast_manager& m, subst_util& subst) :
			m_id(id),
			m_rule(r),
			m_head_func_decl(head_func_decl),
			m_tail_func_decls(tail_func_decls),
			m_uninterp_pos(uninterp_pos),
			m_head_template(head_temp),
			m_tail_templates(tail_temps),
			m_template_pos(temp_pos),
			m_rule_subst(rule_subst),
			m(m),
			m_subst(subst) {}
		unsigned get_tail_size() const {
			return m_tail_func_decls.size();
		}
		func_decl_info* get_decl() const {
			return m_head_func_decl;
		}
		func_decl_info* get_decl(unsigned i) const {
			return m_tail_func_decls[i];
		}
		expr_ref_vector get_non_explicit_args() const;
		expr_ref_vector get_non_explicit_args(unsigned i) const;
		expr_ref_vector get_explicit_args() const;
		expr_ref_vector get_explicit_args(unsigned i) const;
		expr_ref_vector get_body(bool substitute_template_params = true) const;
		used_vars get_used_vars() const;
		friend std::ostream& operator<<(std::ostream& out, rule_info const* ri) {
			out << ri->m_id;
			return out;
		}
	private:
		app* get_head() const {
			return m_rule->get_head();
		}
		app* get_uninterp_tail(unsigned i) const {
			CASSERT("predabst", i < m_uninterp_pos.size());
			return m_rule->get_tail(m_uninterp_pos[i]);
		}
		app* get_template_tail(unsigned i) const {
			CASSERT("predabst", i < m_template_pos.size());
			return m_rule->get_tail(m_template_pos[i]);
		}
	};

	rule_info* make_rule_info(unsigned id, rule* r, obj_map<func_decl, func_decl_info*> const& func_decl2info, ast_manager& m, subst_util& subst);
};

#endif /* _PREDABST_RULE_H_ */
