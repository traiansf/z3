/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

	predabst_input.cpp

Abstract:

	Bounded PREDABST (symbolic simulation using Z3) input processing.

Author:

	Created by James Lingard (jchl) 2015-06-24.

Revision History:

--*/
#include "predabst_util.h"
#include "predabst_rule.h"
#include "predabst_input.h"
#include "dl_rule_set.h"
#include "fixedpoint_params.hpp"

namespace datalog {
	static void failwith(std::string msg) {
		STRACE("predabst", tout << "Malformed input: " << msg << "\n";);
		throw default_exception(msg);
	}

	class builder {
		predabst_input*                     m_input;
		obj_map<func_decl, symbol_info*>    m_func_decl2symbol;
		obj_map<func_decl, template_info*>  m_func_decl2template;
		predabst_input::stats               m_stats;
		subst_util&                         m_subst;
		ast_manager&                        m;

		expr_ref_vector const&              m_template_param_values; // >>> doesn't belong here?
		fixedpoint_params const&            m_fp_params;

	public:
		builder(ast_manager& m, subst_util& subst, expr_ref_vector const& template_param_values, fixedpoint_params const& fp_params) :
			m_input(NULL),
			m_subst(subst),
			m(m),
			m_template_param_values(template_param_values),
			m_fp_params(fp_params) {
		}

		void convert_input(rule_set& rules, predabst_input* input) {
			m_input = input;

			find_all_func_decls(rules);

			// Some of the rules are actually declarations of templates, extra
			// constraints on templates, explicit argument lists, predicate
			// lists, and argument name lists.  Find these, and remove them
			// from the rule set.  Note that we must process the extra template
			// constraints before the templates, in order that we know how many
			// extra arguments each template has; we must process the templates
			// before the explicit argument/argument name/predicate lists, in
			// order to reject such lists for templated predicate symbols; we
			// must process the explicit argument lists before the
			// argument name/predicate lists, in order to reject both
			// predicates that involve explicit arguments and names for
			// explicit arguments; and we must process the argument name lists
			// before the predicate lists, so that we can use the argument
			// names to translate predicates from one predicate symbol to
			// another.
			process_special_rules(rules, is_template_extra, &builder::collect_template_extra);
			process_special_rules(rules, is_template, &builder::collect_template);
			process_special_rules(rules, is_explicit_arg_list, &builder::collect_explicit_arg_list);

			for (unsigned i = 0; i < m_input->m_symbols.size(); ++i) {
				symbol_info* si = m_input->m_symbols[i];
				var_ref_vector vars = get_arg_vars(si->m_fdecl, m);
				for (unsigned j = 0; j < vars.size(); ++j) {
					if (si->m_explicit_args.get(j)) {
						si->m_explicit_vars.push_back(vars.get(j));
					}
					else {
						si->m_abstracted_vars.push_back(vars.get(j));
					}
				}

				if (si->m_is_dwf) {
					CASSERT("predabst", si->m_explicit_args.size() % 2 == 0);
					unsigned n = si->m_explicit_args.size() / 2;
					for (unsigned j = 0; j < n; ++j) {
						if (si->m_explicit_args[j] != si->m_explicit_args[j + n]) {
							failwith("DWF predicate symbol " + si->m_fdecl->get_name().str() + " has arguments " + to_string(j) + " and " + to_string(j + n) + " that are not both explicit or non-explicit");
						}
					}
				}
			}

			process_special_rules(rules, is_arg_name_list, &builder::collect_arg_name_list);
			process_special_rules(rules, is_predicate_list, &builder::collect_predicate_list);

			CASSERT("predabst", m_input->m_rules.empty());
			for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
				rule* r = rules.get_rule(i);
				m_input->m_rules.push_back(make_rule_info(m_input->m_rules.size(), r, m_func_decl2symbol, m_func_decl2template, m));
			}

			for (unsigned i = 0; i < m_input->m_rules.size(); ++i) {
				rule_info* ri = m_input->m_rules[i];
				for (unsigned j = 0; j < ri->get_tail_size(); ++j) {
					ri->get_decl(j)->m_users.insert(ri);
				}
			}

			m_stats.m_num_rules = m_input->m_rules.size();

			STRACE("predabst", print_initial_state(tout););
		}

	private:
		static bool args_are_distinct_vars(app* a, var_ref_vector& vars) {
			vector<bool> used;
			for (unsigned i = 0; i < a->get_num_args(); ++i) {
				if (!is_var(a->get_arg(i))) {
					return false;
				}
				unsigned idx = to_var(a->get_arg(i))->get_idx();
				if (idx >= used.size()) {
					used.resize(idx + 1);
				}
				if (used.get(idx)) {
					return false;
				}
				used[idx] = true;
				vars.push_back(to_var(a->get_arg(i)));
			}
			return true;
		}

		// Returns true if e contains any variables other than those in bound.
		static bool has_free_vars(expr* e, var_ref_vector const& bound) {
			if (is_var(e)) {
				return !bound.contains(to_var(e));
			}
			if (is_app(e)) {
				app* a = to_app(e);
				for (unsigned i = 0; i < a->get_num_args(); ++i) {
					if (has_free_vars(a->get_arg(i), bound)) {
						return true;
					}
				}
			}
			return false;
		}

		// Returns true if e contains any variables.
		bool has_vars(expr* e) const {
			return has_free_vars(e, var_ref_vector(m));
		}

		static bool is_regular_predicate(func_decl const* fdecl) {
			return !is_template_extra(fdecl) &&
				!is_template(fdecl) &&
				!is_explicit_arg_list(fdecl) &&
				!is_explicit_arg(fdecl) &&
				!is_predicate_list(fdecl) &&
				!is_arg_name_list(fdecl) &&
				!is_arg_name(fdecl);
		}

		void find_all_func_decls(rule_set const& rules) {
			for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
				rule* r = rules.get_rule(i);
				func_decl* head_decl = r->get_decl();
				if (is_regular_predicate(head_decl)) {
					process_func_decl(rules, head_decl);

					for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
						func_decl* body_decl = r->get_decl(j);
						if (is_regular_predicate(body_decl)) {
							process_func_decl(rules, body_decl);
						}
						else if (is_template_extra(body_decl)) {
							failwith("found extra template constraint in non-head position");
						}
						else if (is_template(body_decl)) {
							failwith("found template " + body_decl->get_name().str() + " in non-head position");
						}
						else if (is_explicit_arg_list(body_decl)) {
							failwith("found explicit argument list " + body_decl->get_name().str() + " in non-head position");
						}
						else if (is_predicate_list(body_decl)) {
							failwith("found predicate list " + body_decl->get_name().str() + " in non-head position");
						}
						else if (is_arg_name_list(body_decl)) {
							failwith("found argument name list " + body_decl->get_name().str() + " in non-head position");
						}
						else if (is_explicit_arg(body_decl)) {
							failwith("found explicit argument " + body_decl->get_name().str() + " in body of regular rule");
						}
						else if (is_arg_name(body_decl)) {
							failwith("found argument name " + body_decl->get_name().str() + " in body of regular rule");
						}
						else {
							UNREACHABLE();
						}
					}
				}
				else if (is_explicit_arg(head_decl)) {
					failwith("found explicit argument " + head_decl->get_name().str() + " in head position");
				}
				else if (is_arg_name(head_decl)) {
					failwith("found argument name " + head_decl->get_name().str() + " in head position");
				}
			}
		}

		void process_func_decl(rule_set const& rules, func_decl *fdecl) {
			CASSERT("predabst", is_regular_predicate(fdecl));
			CASSERT("predabst", fdecl->get_range() == m.mk_bool_sort());
			if (rules.is_output_predicate(fdecl)) {
				return;
			}

			if (!m_func_decl2symbol.contains(fdecl)) {
				bool is_dwf = is_dwf_predicate(fdecl);
				if (is_dwf) {
					if (fdecl->get_arity() % 2 != 0) {
						failwith("DWF predicate symbol " + fdecl->get_name().str() + " has odd arity");
					}
					for (unsigned i = 0; i < fdecl->get_arity() / 2; ++i) {
						unsigned j = fdecl->get_arity() / 2 + i;
						if (fdecl->get_domain(i) != fdecl->get_domain(j)) {
							failwith("DWF predicate symbol " + fdecl->get_name().str() + " has arguments " + to_string(i) + " and " + to_string(j) + " of unequal types");
						}
						// The following restriction may be removed in future.
						if (fdecl->get_domain(i) != arith_util(m).mk_int()) {
							failwith("DWF predicate symbol " + fdecl->get_name().str() + " has argument " + to_string(i) + " of non-integer type");
						}
					}
				}

				m_input->m_symbols.push_back(alloc(symbol_info, fdecl, is_dwf, m));
				m_func_decl2symbol.insert(fdecl, m_input->m_symbols.back());
				m_stats.m_num_predicate_symbols++;
				m_stats.m_num_predicate_symbol_arguments += fdecl->get_arity();
			}
		}

		bool is_dwf_predicate(func_decl const* pred) const {
			return pred->get_name().str().substr(0, 7) == "__dwf__";
		}

		void process_special_rules(rule_set& rules, bool(*p)(func_decl const*), void (builder::*f)(rule const*)) {
			ptr_vector<rule> to_delete;
			for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
				rule* r = rules.get_rule(i);
				if (p(r->get_decl())) {
					(this->*f)(r);
					to_delete.push_back(r);
				}
			}

			for (unsigned i = 0; i < to_delete.size(); ++i) {
				rules.del_rule(to_delete[i]);
			}
		}

		static bool is_template_extra(func_decl const* fdecl) {
			return fdecl->get_name() == "__temp__extra__";
		}

		void collect_template_extra(rule const* r) {
			CASSERT("predabst", is_template_extra(r->get_decl()));
			// r is a rule of the form:
			//  ??? => __temp__extra__
			// Treat ??? as an extra template constraint.
			func_decl* head_decl = r->get_decl();
			STRACE("predabst", tout << "Found extra template constraint with " << head_decl->get_arity() << " parameters\n";);
			CASSERT("predabst", head_decl->get_range() == m.mk_bool_sort());

			if (m_input->m_template_params.size() > 0) {
				failwith("found multiple extra template constraints");
			}

			var_ref_vector args(m);
			if (!args_are_distinct_vars(r->get_head(), args)) {
				failwith("extra template constraint has invalid argument list");
			}

			if (r->get_uninterpreted_tail_size() != 0) {
				failwith("extra template constraint has an uninterpreted tail");
			}

			// Replace the variables corresponding to the extra template parameters with fresh constants.
			expr_ref_vector extra_params = get_arg_fresh_consts(r->get_decl(), "b", m);
			expr_ref_vector extra_subst = m_subst.build(args, extra_params);
			expr_ref extras = m_subst.apply(mk_conj(expr_ref_vector(m, r->get_tail_size(), r->get_expr_tail())), extra_subst);
			STRACE("predabst", tout << "  " << mk_pp(extras, m) << "\n";);

			if (has_vars(extras)) {
				failwith("extra template constraint has free variables");
			}

			CASSERT("predabst", m_input->m_template_params.empty());
			m_input->m_template_params.swap(extra_params);
			CASSERT("predabst", !m_input->m_template_extras);
			m_input->m_template_extras = extras;
			m_stats.m_num_template_params = m_input->m_template_params.size();
		}

		static bool is_template(func_decl const* fdecl) {
			return (fdecl->get_name().str().substr(0, 8) == "__temp__") && !is_template_extra(fdecl);
		}

		void collect_template(rule const* r) {
			CASSERT("predabst", is_template(r->get_decl()));
			// r is a rule of the form:
			//  ??? => __temp__SUFFIX
			// Treat ??? as a template for predicate symbol SUFFIX.
			func_decl* head_decl = r->get_decl();
			symbol suffix(head_decl->get_name().str().substr(8).c_str());
			if (suffix.str().empty()) {
				failwith("found template for predicate symbol with zero-length name");
			}

			STRACE("predabst", tout << "Found template for predicate symbol " << suffix << "\n";);

			unsigned num_extras = m_input->m_template_params.size();
			if (head_decl->get_arity() < num_extras) {
				failwith("template for " + suffix.str() + " has insufficient parameters");
			}

			unsigned new_arity = head_decl->get_arity() - num_extras;
			for (unsigned i = 0; i < num_extras; ++i) {
				if (head_decl->get_domain(new_arity + i) != get_sort(m_input->m_template_params.get(i))) {
					failwith("extra parameter " + to_string(i) + " to template for " + suffix.str() + " is of wrong type");
				}
			}

			func_decl_ref suffix_decl(m.mk_func_decl(
				suffix,
				new_arity,
				head_decl->get_domain(),
				head_decl->get_range()), m);
			if (m_func_decl2template.contains(suffix_decl)) {
				failwith("found multiple templates for " + suffix.str());
			}
			if (!m_func_decl2symbol.contains(suffix_decl)) {
				failwith("found template for non-existent predicate symbol " + suffix.str());
			}

			symbol_info* si = m_func_decl2symbol[suffix_decl];
			if (si->m_is_dwf) {
				failwith("found template for DWF predicate symbol " + suffix.str());
			}

			var_ref_vector args(m);
			if (!args_are_distinct_vars(r->get_head(), args)) {
				failwith("template for " + suffix.str() + " has invalid argument list");
			}

			if (r->get_uninterpreted_tail_size() != 0) {
				failwith("template for " + suffix.str() + " has an uninterpreted tail");
			}

			var_ref_vector vars = get_arg_vars(r->get_decl(), m);
			expr_ref_vector subst = m_subst.build(args, vars);
			expr_ref_vector body(m);
			for (unsigned i = 0; i < r->get_tail_size(); ++i) {
				if (has_free_vars(r->get_tail(i), args)) {
					failwith("template for " + suffix.str() + " has free variables");
				}
				body.push_back(m_subst.apply(r->get_tail(i), subst));
			}
			STRACE("predabst", tout << "  " << suffix_decl->get_name() << "(" << vars << ") := " << body << "\n";);
			m_input->m_templates.push_back(alloc(template_info, suffix_decl, vars, body, m_input->m_template_params, m_template_param_values, m_subst));
			m_func_decl2template.insert(suffix_decl, m_input->m_templates.back());
			m_stats.m_num_templates++;

			m_input->m_symbols.erase(si);
			m_func_decl2symbol.remove(suffix_decl);
			dealloc(si);
		}

		static bool is_explicit_arg_list(func_decl const* fdecl) {
			return fdecl->get_name().str().substr(0, 11) == "__expargs__";
		}

		static bool is_explicit_arg(func_decl const* fdecl) {
			return fdecl->get_name().str() == "__exparg__";
		}

		void collect_explicit_arg_list(rule const* r) {
			CASSERT("predabst", is_explicit_arg_list(r->get_decl()));
			// r is a rule of the form:
			//   __exparg__(xi) AND ... AND __exparg__(xj) => __expargs__SUFFIX(x1, ..., xN)
			// Treat xi,...,xj as explicit arguments for SUFFIX.
			func_decl* head_decl = r->get_decl();
			symbol suffix(head_decl->get_name().str().substr(11).c_str());
			if (suffix.str().empty()) {
				failwith("found explicit argument list for predicate symbol with zero-length name");
			}

			STRACE("predabst", tout << "Found explicit argument list for predicate symbol " << suffix << "(" << expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()) << ")\n";);

			func_decl_ref suffix_decl(m.mk_func_decl(
				suffix,
				head_decl->get_arity(),
				head_decl->get_domain(),
				head_decl->get_range()), m);
			if (m_func_decl2template.contains(suffix_decl)) {
				failwith("found explicit argument list for templated predicate symbol " + suffix.str());
			}
			if (!m_func_decl2symbol.contains(suffix_decl)) {
				failwith("found explicit argument list for non-existent predicate symbol " + suffix.str());
			}

			symbol_info* si = m_func_decl2symbol[suffix_decl];

			var_ref_vector args(m);
			if (!args_are_distinct_vars(r->get_head(), args)) {
				failwith("explicit argument list for " + suffix.str() + " has invalid argument list");
			}

			if (r->get_tail_size() != r->get_uninterpreted_tail_size()) {
				failwith("explicit argument list for " + suffix.str() + " has an interpreted tail");
			}

			for (unsigned i = 0; i < r->get_tail_size(); ++i) {
				app_ref tail(r->get_tail(i), m);
				if (!is_explicit_arg(tail->get_decl())) {
					failwith("explicit argument list for " + suffix.str() + " has unexpected predicate in uninterpreted tail");
				}
				CASSERT("predabst", get_sort(tail) == m.mk_bool_sort());
				if (tail->get_decl()->get_arity() != 1) {
					failwith("explicit argument list for " + suffix.str() + " has __exparg__ predicate of incorrect arity");
				}
				if (!is_var(tail->get_arg(0))) {
					failwith("explicit argument list for " + suffix.str() + " has __exparg__ predicate with non-variable argument");
				}
				var_ref v(to_var(tail->get_arg(0)), m);
				if (!args.contains(v)) {
					failwith("explicit argument list for " + suffix.str() + " has __exparg__ predicate with argument that does not appear in the head");
				}
				unsigned j = vector_find(args, v.get());
				if (si->m_explicit_args.get(j)) {
					failwith("explicit argument list for " + suffix.str() + " has duplicate __exparg__ declaration for argument " + to_string(j));
				}
				m_stats.m_num_explicit_arguments++;
				if (m_fp_params.use_exp_eval()) {
					STRACE("predabst", tout << "Found explicit argument declaration for argument " << j << "\n";);
					si->m_explicit_args[j] = true;
				}
				else {
					STRACE("predabst", tout << "Ignoring explicit argument declaration for argument " << j << "\n";);
				}
			}
		}

		static bool is_arg_name_list(func_decl const* fdecl) {
			return fdecl->get_name().str().substr(0, 9) == "__names__";
		}

		static bool is_arg_name(func_decl const* fdecl) {
			return fdecl->get_name().str().substr(0, 8) == "__name__";
		}

		void collect_arg_name_list(rule const* r) {
			CASSERT("predabst", is_arg_name_list(r->get_decl()));
			// r is a rule of the form:
			//   __name_a1(x1) AND ... AND __name_aN(xN) => __names__SUFFIX(x1, ..., xN)
			// Treat a1..aN as the names of the arguments for SUFFIX.
			func_decl* head_decl = r->get_decl();
			symbol suffix(head_decl->get_name().str().substr(9).c_str());
			if (suffix.str().empty()) {
				failwith("found argument name list for predicate symbol with zero-length name");
			}

			STRACE("predabst", tout << "Found argument name list for predicate symbol " << suffix << "(" << expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()) << ")\n";);

			func_decl_ref suffix_decl(m.mk_func_decl(
				suffix,
				head_decl->get_arity(),
				head_decl->get_domain(),
				head_decl->get_range()), m);
			if (m_func_decl2template.contains(suffix_decl)) {
				failwith("found argument name list for templated predicate symbol " + suffix.str());
			}
			if (!m_func_decl2symbol.contains(suffix_decl)) {
				failwith("found argument name list for non-existent predicate symbol " + suffix.str());
			}

			symbol_info* si = m_func_decl2symbol[suffix_decl];

			var_ref_vector args(m);
			if (!args_are_distinct_vars(r->get_head(), args)) {
				failwith("argument name list for " + suffix.str() + " has invalid argument list");
			}

			if (r->get_tail_size() != r->get_uninterpreted_tail_size()) {
				failwith("argument name list for " + suffix.str() + " has an interpreted tail");
			}

			for (unsigned i = 0; i < r->get_tail_size(); ++i) {
				app_ref tail(r->get_tail(i), m);
				if (!is_arg_name(tail->get_decl())) {
					failwith("argument name list for " + suffix.str() + " has unexpected predicate in uninterpreted tail");
				}
				CASSERT("predabst", get_sort(tail) == m.mk_bool_sort());
				if (tail->get_decl()->get_arity() != 1) {
					failwith("argument name list for " + suffix.str() + " has __name__X predicate of incorrect arity");
				}
				if (!is_var(tail->get_arg(0))) {
					failwith("argument name list for " + suffix.str() + " has __name__X predicate with non-variable argument");
				}
				var_ref v(to_var(tail->get_arg(0)), m);
				if (!args.contains(v)) {
					failwith("argument name list for " + suffix.str() + " has __name__X predicate with argument that does not appear in the head");
				}
				unsigned j = vector_find(args, v.get());
				if (si->m_var_names.get(j)) {
					failwith("argument name list for " + suffix.str() + " has duplicate name for argument " + to_string(j));
				}
				symbol name(tail->get_decl()->get_name().str().substr(8).c_str());
				if (name.str().empty()) {
					failwith("argument name list for " + suffix.str() + " has zero-length name for argument " + to_string(j));
				}
				func_decl_ref name_decl(m.mk_const_decl(name, args.get(j)->get_sort()), m);
				if (si->m_var_names.contains(name_decl)) {
					failwith("argument name list for " + suffix.str() + " has non-unique name for argument " + to_string(j));
				}
				m_stats.m_num_named_arguments++;
				if (si->m_explicit_args.get(j)) {
					STRACE("predabst", tout << "Ignoring name for explicit argument " << j << "\n";);
				}
				else {
					STRACE("predabst", tout << "Found name " << name << " for argument " << j << "\n";);
					si->m_var_names[j] = name_decl;
				}
			}
		}

		static bool is_predicate_list(func_decl const* fdecl) {
			return fdecl->get_name().str().substr(0, 8) == "__pred__";
		}

		void collect_predicate_list(rule const* r) {
			CASSERT("predabst", is_predicate_list(r->get_decl()));
			// r is a rule of the form:
			//   p1 AND ... AND pN => __pred__SUFFIX
			// Treat p1...pN as initial predicates for predicate symbol SUFFIX.
			func_decl* head_decl = r->get_decl();
			symbol suffix(head_decl->get_name().str().substr(8).c_str());
			if (suffix.str().empty()) {
				failwith("found predicate list for predicate symbol with zero-length name");
			}

			STRACE("predabst", tout << "Found predicate list for predicate symbol " << suffix << "(" << expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()) << ")\n";);

			func_decl_ref suffix_decl(m.mk_func_decl(
				suffix,
				head_decl->get_arity(),
				head_decl->get_domain(),
				head_decl->get_range()), m);
			if (m_func_decl2template.contains(suffix_decl)) {
				failwith("found predicate list for templated predicate symbol " + suffix.str());
			}
			if (!m_func_decl2symbol.contains(suffix_decl)) {
				failwith("found predicate list for non-existent predicate symbol " + suffix.str());
			}

			symbol_info* si = m_func_decl2symbol[suffix_decl];

			var_ref_vector args(m);
			if (!args_are_distinct_vars(r->get_head(), args)) {
				failwith("predicate list for " + suffix.str() + " has invalid argument list");
			}

			var_ref_vector abstracted_args(m);
			for (unsigned i = 0; i < args.size(); ++i) {
				if (!si->m_explicit_args.get(i)) {
					abstracted_args.push_back(args.get(i));
				}
			}

			if (r->get_uninterpreted_tail_size() != 0) {
				failwith("predicate list for " + suffix.str() + " has an uninterpreted tail");
			}

			// Add p1..pN to m_func_decl2symbol[SUFFIX].m_preds.
			expr_ref_vector subst = m_subst.build(abstracted_args, si->m_abstracted_vars);
			for (unsigned i = 0; i < r->get_tail_size(); ++i) {
				if (has_free_vars(r->get_tail(i), args)) {
					failwith("predicate for " + suffix.str() + " has free variables");
				}
				if (has_free_vars(r->get_tail(i), abstracted_args)) {
					failwith("predicate for " + suffix.str() + " uses explicit arguments");
				}

				expr_ref pred = m_subst.apply(to_expr(r->get_tail(i)), subst);
				STRACE("predabst", tout << "  predicate " << i << ": " << mk_pp(pred, m) << "\n";);
				m_stats.m_num_initial_predicates++;
				si->m_initial_preds.push_back(pred);
			}
		}

		void print_initial_state(std::ostream& out) const {
			out << "=====================================\n";
			out << "Initial state:\n";
			out << "  Symbols:" << std::endl;
			for (unsigned i = 0; i < m_input->m_symbols.size(); ++i) {
				symbol_info const* si = m_input->m_symbols[i];
				out << "    " << si << " is used by rules " << si->m_users << std::endl;
			}
			out << "  Templates:" << std::endl;
			for (unsigned i = 0; i < m_input->m_templates.size(); ++i) {
				template_info const* ti = m_input->m_templates[i];
				out << "    " << ti << "(" << ti->m_vars << ") := " << ti->m_body << std::endl;
			}
			out << "  Rules:" << std::endl;
			for (unsigned i = 0; i < m_input->m_rules.size(); ++i) {
				rule_info const* ri = m_input->m_rules[i];
				out << "    " << ri << ": ";
				ri->display_smt2(out);
				out << std::endl;
			}
			out << "=====================================\n";
		}
	};

	predabst_input* make_predabst_input(rule_set& rules, ast_manager& m, subst_util& subst, expr_ref_vector const& template_param_values, fixedpoint_params const& fp_params) {
		predabst_input* input = alloc(predabst_input, m);
		try {
			builder b(m, subst, template_param_values, fp_params);
			b.convert_input(rules, input);
			return input;
		}
		catch (...) {
			dealloc(input);
			throw;
		}
	}
}
