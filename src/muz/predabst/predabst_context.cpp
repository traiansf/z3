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
#include "predabst_context.h"
#include "dl_context.h"
#include "unifier.h"
#include "var_subst.h"
#include "simplifier.h"
#include "arith_simplifier_plugin.h"
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
#include <vector>
#include <map>
#include <algorithm>

#undef PREDABST_SOLVER_PER_RULE

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
            out << solution.m_head << " := " << mk_pp(solution.m_body, solution.m_body.m());
            return out;
        }
    };

    typedef vector<core_clause> core_clauses; // just a sequence; the index has no meaning
    typedef vector<core_clause_solution> core_clause_solutions; // ditto

    class predabst::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            // Statistics about the input.
            unsigned m_num_predicate_symbols;
            unsigned m_num_predicate_symbol_arguments;
            unsigned m_num_explicit_arguments;
            unsigned m_num_named_arguments;
            unsigned m_num_template_params;
            unsigned m_num_templates;
            unsigned m_num_initial_predicates;
            unsigned m_num_rules;

            // Overall statistics.
            unsigned m_num_refinement_iterations;
            unsigned m_num_template_instantiations;

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

            // Statistics about refinement.
            unsigned m_num_predicates_added;
            unsigned m_num_predicates_added_query_naming;
        };

        class scoped_push {
            smt::kernel& s;
        public:
            scoped_push(smt::kernel& s) : s(s) { s.push(); }
            ~scoped_push() { s.pop(1); }
        };

		struct rule_info;
		struct node_info;
		struct template_info;

        typedef vector<bool> cube_t;
		typedef vector<rule_info const*> rule_vector;
		typedef vector<node_info const*> node_vector;

        struct func_decl_info {
            func_decl*           m_fdecl;
            var_ref_vector       m_vars;
            expr_ref_vector      m_preds;
            unsigned             m_new_preds;
            func_decl_ref_vector m_var_names;
            vector<bool>         m_explicit_args;
            var_ref_vector       m_explicit_vars;
            var_ref_vector       m_non_explicit_vars;
            rule_vector          m_users;
            node_vector          m_max_reach_nodes;
            bool                 m_is_dwf_predicate;
            bool                 m_has_template;
            template_info*       m_template;
            func_decl_info(func_decl* fdecl, var_ref_vector const& vars, bool is_dwf_predicate) :
                m_fdecl(fdecl),
                m_vars(vars),
                m_preds(vars.m()),
                m_new_preds(0),
                m_var_names(vars.m()),
                m_explicit_vars(vars.m()),
                m_non_explicit_vars(vars.m()),
                m_is_dwf_predicate(is_dwf_predicate),
                m_has_template(false),
                m_template(NULL) {
                m_var_names.reserve(vars.size());
                m_explicit_args.reserve(vars.size());
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
        };

        struct rule_instance_info {
#ifdef PREDABST_SOLVER_PER_RULE
            smt::kernel*            m_rule_solver;
#endif
            expr_ref_vector         m_body;
            expr_ref_vector         m_head_preds;
            expr_ref_vector         m_head_explicit_args;
            vector<bool>            m_head_known_args;
            unsigned                m_num_head_unknown_args;
            vector<expr_ref_vector> m_body_preds;
            vector<expr_ref_vector> m_body_explicit_args;
            vector<vector<bool>>    m_body_known_args;
            rule_instance_info(ast_manager& m) :
#ifdef PREDABST_SOLVER_PER_RULE
                m_rule_solver(NULL),
#endif
                m_body(m),
                m_head_preds(m),
                m_head_explicit_args(m) {}
            void reset() {
#ifdef PREDABST_SOLVER_PER_RULE
                m_rule_solver->reset();
#endif
                m_body.reset();
                m_head_preds.reset();
                m_head_explicit_args.reset();
                m_head_known_args.reset();
                m_body_preds.reset();
                m_body_explicit_args.reset();
                m_body_known_args.reset();
            }
#ifdef PREDABST_SOLVER_PER_RULE
            void cancel() {
                m_rule_solver->cancel();
            }
            void reset_cancel() {
                m_rule_solver->reset_cancel();
            }
            void alloc_solver(ast_manager& m, smt_params& fparams) {
                CASSERT("predabst", !m_rule_solver);
                m_rule_solver = alloc(smt::kernel, m, fparams);
                set_logic(m_rule_solver); // >>> won't compile any more
            }
            void dealloc_solver() {
                CASSERT("predabst", m_rule_solver);
                dealloc(m_rule_solver);
                m_rule_solver = NULL;
            }
#endif
            void display(std::ostream& out, rule_info const* ri, imp const* _this) const {
                out << "      head preds (" << ri->get_decl(_this) << "): " << m_head_preds << "\n";
                CASSERT("predabst", ri->get_tail_size() == m_body_preds.size());
                for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                    out << "      body preds " << i << " (" << ri->get_decl(i, _this) << "): " << m_body_preds[i] << "\n";
                }
                out << "      head explicit args (" << ri->get_decl(_this) << "): " << m_head_explicit_args << "\n";
                CASSERT("predabst", ri->get_tail_size() == m_body_explicit_args.size());
                for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                    out << "      body explicit args " << i << " (" << ri->get_decl(i, _this) << "): " << m_body_explicit_args[i] << "\n";
                }
                out << "      body: " << m_body << "\n";
            }
        };

        inline smt::kernel* solver_for(rule_info const* ri) {
#ifdef PREDABST_SOLVER_PER_RULE
            return ri->m_instance_info.m_rule_solver;
#else
            return &m_solver;
#endif
        }

        struct rule_info {
            unsigned                m_id;
            rule*                   m_rule;
            vector<unsigned>        m_uninterp_pos;
            expr_ref_vector         m_rule_subst;
            rule_instance_info      m_instance_info;
            bool                    m_unsat;
            ast_manager&            m;
            rule_info(unsigned id, rule* r, expr_ref_vector& rule_subst, ast_manager& m) :
                m_id(id),
                m_rule(r),
                m_rule_subst(m),
                m_instance_info(m),
                m(m) {
                m_rule_subst.swap(rule_subst);
            }
            unsigned get_tail_size() const {
                return m_uninterp_pos.size();
            }
            app* get_head() const {
                return m_rule->get_head();
            }
            app* get_tail(unsigned i) const {
                CASSERT("predabst", i < m_uninterp_pos.size());
                return m_rule->get_tail(m_uninterp_pos[i]);
            }
            func_decl_info* get_decl(imp const* _this) const {
                if (has_head(_this)) {
                    return _this->m_func_decl2info[get_head()->get_decl()];
                }
                else {
                    return NULL;
                }
            }
            func_decl_info* get_decl(unsigned i, imp const* _this) const {
                CASSERT("predabst", has_tail(i, _this));
                return _this->m_func_decl2info[get_tail(i)->get_decl()];
            }
            unsigned get_arity(imp const* _this) const {
                if (has_head(_this)) {
                    return get_head()->get_decl()->get_arity();
                }
                else {
                    return 0;
                }
            }
            unsigned get_arity(unsigned i, imp const* _this) const {
                CASSERT("predabst", has_tail(i, _this));
                return get_tail(i)->get_decl()->get_arity();
            }
            expr_ref_vector get_non_explicit_args(imp const* _this) const {
                if (has_head(_this)) {
                    expr_ref_vector args(m);
                    for (unsigned i = 0; i < get_head()->get_num_args(); ++i) {
                        if (!get_decl(_this)->m_explicit_args.get(i)) {
                            args.push_back(get_head()->get_arg(i));
                        }
                    }
                    return args;
                }
                else {
                    return expr_ref_vector(m);
                }
            }
            expr_ref_vector get_non_explicit_args(unsigned i, imp const* _this) const {
                CASSERT("predabst", has_tail(i, _this));
                expr_ref_vector args(m);
                for (unsigned j = 0; j < get_tail(i)->get_num_args(); ++j) {
                    if (!get_decl(i, _this)->m_explicit_args.get(j)) {
                        args.push_back(get_tail(i)->get_arg(j));
                    }
                }
                return args;
            }
            expr_ref_vector get_explicit_args(imp const* _this) const {
                if (has_head(_this)) {
                    expr_ref_vector args(m);
                    for (unsigned i = 0; i < get_head()->get_num_args(); ++i) {
                        if (get_decl(_this)->m_explicit_args.get(i)) {
                            args.push_back(get_head()->get_arg(i));
                        }
                    }
                    return args;
                }
                else {
                    return expr_ref_vector(m);
                }
            }
            expr_ref_vector get_explicit_args(unsigned i, imp const* _this) const {
                CASSERT("predabst", has_tail(i, _this));
                expr_ref_vector args(m);
                for (unsigned j = 0; j < get_tail(i)->get_num_args(); ++j) {
                    if (get_decl(i, _this)->m_explicit_args.get(j)) {
                        args.push_back(get_tail(i)->get_arg(j));
                    }
                }
                return args;
            }
            friend std::ostream& operator<<(std::ostream& out, rule_info const* ri) {
                out << ri->m_id;
                return out;
            }
        private:
            bool has_head(imp const* _this) const {
                return _this->m_func_decl2info.contains(get_head()->get_decl()) &&
                    !_this->m_func_decl2info[get_head()->get_decl()]->m_has_template;
            }
            bool has_tail(unsigned i, imp const* _this) const {
                return _this->m_func_decl2info.contains(get_tail(i)->get_decl()) &&
                    !_this->m_func_decl2info[get_tail(i)->get_decl()]->m_has_template;
            }
        };

        struct node_info {
            unsigned         m_id;
            func_decl_info*  m_fdecl_info;
            cube_t           m_cube;
            expr_ref_vector  m_explicit_values;
            rule_info const* m_parent_rule;
            node_vector      m_parent_nodes;
            node_info(unsigned id, func_decl_info* fdecl_info, cube_t const& cube, expr_ref_vector const& explicit_values, rule_info const* parent_rule, node_vector const& parent_nodes) :
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

        struct template_info {
            var_ref_vector  m_vars;
            expr_ref_vector m_body;
            template_info(var_ref_vector const& vars, expr_ref_vector const& body) :
                m_vars(vars),
                m_body(body) {}
        };

        static const unsigned NON_NODE = UINT_MAX;

        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        fixedpoint_params const& m_fp_params;
        smt_params             m_fparams;     // parameters specific to smt solving
#ifndef PREDABST_SOLVER_PER_RULE
        smt::kernel            m_solver;      // basic SMT solver class
#endif
        mutable var_subst      m_var_subst;   // substitution object. It gets updated and reset.
        mutable simplifier     m_simplifier;
		mutable smt::kernel* volatile m_current_solver;
        bool volatile          m_cancel;      // Boolean flag to track external cancelation.
        mutable stats          m_stats;       // statistics information specific to the predabst module.

		obj_map<func_decl, func_decl_info*> m_func_decl2info;
		vector<func_decl_info*>             m_func_decls;
        vector<rule_info*>                  m_rules;
        vector<node_info*>                  m_nodes;
        node_vector                         m_node_worklist;

        expr_ref_vector                     m_template_params;
        expr_ref_vector                     m_template_param_values;
        expr_ref                            m_template_extras;
        vector<template_info*>              m_templates;
        expr_ref_vector                     m_template_constraint_vars;
        expr_ref_vector                     m_template_constraints;

        typedef enum { reached_query, not_wf } acr_error_kind;

        struct acr_error {
            node_info const* m_node;
            acr_error_kind   m_kind;
            acr_error() {}
            acr_error(node_info const* node, acr_error_kind kind) :
                m_node(node),
                m_kind(kind) {}
        };

        struct core_tree_info {
            unsigned m_count;
            core_tree_info() :
                m_count(0) {}
        };

        struct core_tree_template_info {
            expr_ref m_body;
            core_tree_template_info(ast_manager& m) :
                m_body(m) {}
        };

        struct core_tree_wf_info {
            expr_ref         m_bound;
            expr_ref         m_decrease;
            core_tree_wf_info(ast_manager& m) :
                m_bound(m),
                m_decrease(m) {}
        };

    public:
        imp(ast_manager& m, fixedpoint_params const& fp_params) :
            m(m),
            m_fp_params(fp_params),
#ifndef PREDABST_SOLVER_PER_RULE
            m_solver(m, m_fparams),
#endif
            m_var_subst(m, false),
            m_simplifier(m),
            m_cancel(false),
			m_current_solver(NULL),
            m_template_params(m),
            m_template_param_values(m),
            m_template_extras(m),
            m_template_constraints(m),
            m_template_constraint_vars(m) {

            m_fparams.m_mbqi = false;
            m_fparams.m_model = false;
			if (m_fp_params.no_simplify()) {
				m_fparams.m_preprocess = false;
			}
            set_logic(m_solver);

			if (m_fp_params.pre_simplify()) {
				basic_simplifier_plugin* bsimp = alloc(basic_simplifier_plugin, m);
				m_simplifier.register_plugin(bsimp);
				m_simplifier.register_plugin(alloc(arith_simplifier_plugin, m, *bsimp, m_fparams));
			}

            reg_decl_plugins(m);
        }

        ~imp() {
#ifdef PREDABST_SOLVER_PER_RULE
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				m_rules[i]->m_instance_info.dealloc_solver();
			}
#endif
			for (unsigned i = 0; i < m_func_decls.size(); ++i) {
				dealloc(m_func_decls[i]);
			}
			for (unsigned i = 0; i < m_rules.size(); ++i) {
				dealloc(m_rules[i]);
			}
			for (unsigned i = 0; i < m_nodes.size(); ++i) {
				dealloc(m_nodes[i]);
			}
			for (unsigned i = 0; i < m_templates.size(); ++i) {
				dealloc(m_templates[i]);
			}
        }

        lbool query(rule_set& rules) {
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
            process_special_rules(rules, is_template_extra, &imp::collect_template_extra);
            process_special_rules(rules, is_template, &imp::collect_template);
            process_special_rules(rules, is_explicit_arg_list, &imp::collect_explicit_arg_list);

            for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                func_decl_info* fi = m_func_decls[i];
                for (unsigned j = 0; j < fi->m_vars.size(); ++j) { // >>> could almost avoid m_vars completely at this point...
                    if (fi->m_explicit_args.get(j)) {
                        fi->m_explicit_vars.push_back(fi->m_vars.get(j));
                    }
                    else {
                        fi->m_non_explicit_vars.push_back(fi->m_vars.get(j));
                    }
                }

                if (fi->m_is_dwf_predicate) {
                    CASSERT("predabst", fi->m_explicit_args.size() % 2 == 0);
                    unsigned n = fi->m_explicit_args.size() / 2;
                    for (unsigned j = 0; j < n; ++j) {
                        if (fi->m_explicit_args[j] != fi->m_explicit_args[j + n]) {
                            STRACE("predabst", tout << "Error: DWF predicate symbol has non-pairwise explicit arguments\n";);
                            throw default_exception("DWF predicate symbol " + fi->m_fdecl->get_name().str() + " has non-pairwise explicit arguments");
                        }
                    }
                }
            }

            process_special_rules(rules, is_arg_name_list, &imp::collect_arg_name_list);
			process_special_rules(rules, is_predicate_list, &imp::collect_predicate_list);

            CASSERT("predabst", m_rules.empty());
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                m_rules.push_back(alloc(rule_info, m_rules.size(), r, get_subst_vect_free(r, "c"), m));
                rule_info* ri = m_rules.back();
#ifdef PREDABST_SOLVER_PER_RULE
                ri->m_instance_info.alloc_solver(m, m_fparams);
#endif

                CASSERT("predabst", is_regular_predicate(r->get_decl()));
                for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                    CASSERT("predabst", is_regular_predicate(r->get_decl(j)));
                    if (!m_func_decl2info[r->get_decl(j)]->m_has_template) {
                        ri->m_uninterp_pos.push_back(j);
                        m_func_decl2info[r->get_decl(j)]->m_users.insert(ri);
                    }
                }
            }

            m_stats.m_num_rules = m_rules.size();

            return abstract_check_refine();
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
#define UPDATE_STAT(NAME) st.update(#NAME, m_stats.m_ ## NAME)
            UPDATE_STAT(num_predicate_symbols);
            UPDATE_STAT(num_predicate_symbol_arguments);
            UPDATE_STAT(num_explicit_arguments);
            UPDATE_STAT(num_named_arguments);
            UPDATE_STAT(num_template_params);
            UPDATE_STAT(num_templates);
            UPDATE_STAT(num_initial_predicates);
            UPDATE_STAT(num_rules);
            UPDATE_STAT(num_refinement_iterations);
            UPDATE_STAT(num_template_instantiations);
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
            UPDATE_STAT(num_predicates_added);
            UPDATE_STAT(num_predicates_added_query_naming);
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
            for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                func_decl_info const* fi = m_func_decls[i];
                // Note that the generated model must be in terms of
                // get_arg_vars(fi->m_fdecl); we generate the model in terms of
                // fi->m_vars, which we assume to be the same.
                if (fi->m_has_template) {
                    // templated predicate symbols are instantiated
                    template_info const* temp = fi->m_template;
                    expr_ref_vector temp_subst = get_temp_subst_vect(temp, fi->m_vars);
                    expr_ref body = mk_conj(apply_subst(temp->m_body, temp_subst));
                    register_decl(md, fi, body);
                }
                else {
                    // other predicate symbols are concretized
                    node_vector const& nodes = fi->m_max_reach_nodes;
                    expr_ref_vector disj(m);
                    for (node_vector::const_iterator it = nodes.begin(); it != nodes.end(); ++it) {
                        node_info const* node = *it;
                        disj.push_back(node_to_formula(node));
                    }
                    register_decl(md, fi, mk_disj(disj));
                }
            }
            return md;
        }

    private:

        // Returns true if v1 is a (possibly non-strict) subset of v2.
        template<typename T>
        static bool is_subset(T const& v1, T const& v2) {
            for (unsigned i = 0; i < v1.size(); ++i) {
                if (!v2.contains(v1.get(i))) {
                    return false;
                }
            }
            return true;
        }

        // Apply a substitution vector to an expression, returning the result.
        expr_ref apply_subst(expr* expr, expr_ref_vector const& subst) const {
            expr_ref expr2(m);
            m_var_subst(expr, subst.size(), subst.c_ptr(), expr2);
            return expr2;
        }

        // Apply a substitution vector to an application expression, returning the result.
        app_ref apply_subst(app* app, expr_ref_vector const& subst) const {
            expr_ref expr2(m);
            m_var_subst(app, subst.size(), subst.c_ptr(), expr2);
            return app_ref(to_app(expr2), m);
        }

        // Apply a substitution vector to each expression in a vector of
        // expressions, returning the result.
        expr_ref_vector apply_subst(expr_ref_vector const& exprs, expr_ref_vector const& subst) const {
            expr_ref_vector exprs2(m);
            exprs2.reserve(exprs.size());
            for (unsigned i = 0; i < exprs.size(); ++i) {
                exprs2[i] = apply_subst(exprs[i], subst);
            }
            return exprs2;
        }

        // Returns a substitution vector that maps each variable in vars to the
        // corresponding expression in exprs.
        expr_ref_vector build_subst(unsigned n, var* const* vars, expr* const* exprs) const {
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

        expr_ref_vector build_subst(var* const* vars, expr_ref_vector const& exprs) const {
            return build_subst(exprs.size(), vars, exprs.c_ptr());
        }

        expr_ref_vector build_subst(var_ref_vector const& vars, expr* const* exprs) const {
            return build_subst(vars.size(), vars.c_ptr(), exprs);
        }

        expr_ref_vector build_subst(var_ref_vector const& vars, expr_ref_vector const& exprs) const {
            CASSERT("predabst", vars.size() == exprs.size());
            return build_subst(vars.size(), vars.c_ptr(), exprs.c_ptr());
        }

        expr_ref_vector build_subst(var_ref_vector const& vars, var_ref_vector const& exprs) const {
            CASSERT("predabst", vars.size() == exprs.size());
            return build_subst(vars.size(), vars.c_ptr(), (expr* const*)exprs.c_ptr());
        }

        expr_ref_vector get_fresh_args(func_decl_info const* fi, char const* prefix) const {
            if (fi) {
                expr_ref_vector args = get_fresh_args(fi->m_fdecl, prefix);
                expr_ref_vector non_explicit_args(m);
                for (unsigned i = 0; i < fi->m_explicit_args.size(); ++i) {
                    if (!fi->m_explicit_args.get(i)) {
                        non_explicit_args.push_back(args.get(i));
                    }
                }
                return non_explicit_args;
            }
            else {
                return expr_ref_vector(m);
            }
        }

        // Returns a vector of fresh constants of the right type to be arguments to fdecl.
        expr_ref_vector get_fresh_args(func_decl* fdecl, char const* prefix) const {
            expr_ref_vector args(m);
            args.reserve(fdecl->get_arity());
            for (unsigned i = 0; i < fdecl->get_arity(); ++i) {
                args[i] = m.mk_fresh_const(prefix, fdecl->get_domain(i));
            }
            return args;
        }

        // Returns a vector of variables of the right type to be arguments to fdecl.
        var_ref_vector get_arg_vars(func_decl* fdecl) const {
            var_ref_vector args(m);
            args.reserve(fdecl->get_arity());
            for (unsigned i = 0; i < fdecl->get_arity(); ++i) {
                args[i] = m.mk_var(i, fdecl->get_domain(i));
            }
            return args;
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) covering all the variables used by r, which maps the variables
        // used as head arguments to hvars, and maps all variables that do not
        // appear in the head to fresh constants.
        expr_ref_vector get_subst_vect(rule_info const* ri, expr_ref_vector const& hvars, expr_ref_vector const& hvalues, vector<expr_ref_vector> const& bvalues, char const* prefix, expr_ref_vector& unification_terms) const {
            used_vars used;
            // The following is a clone of r->get_used_vars(&used), which is unfortunately inaccessible.
            used.process(ri->m_rule->get_head());
            for (unsigned i = 0; i < ri->m_rule->get_tail_size(); ++i) {
                used.process(ri->m_rule->get_tail(i));
            }

            expr_ref_vector rule_subst(m);
            rule_subst.reserve(used.get_max_found_var_idx_plus_1());

            // Variables that appear bare in the non-explicit head are mapped to the first corresponding argument.
            vector<bool> constraint_needed;
            expr_ref_vector head_args = ri->get_non_explicit_args(this);
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
            expr_ref_vector head_eargs = ri->get_explicit_args(this);
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
                expr_ref_vector body_eargs = ri->get_explicit_args(i, this);
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
                    unification_terms.push_back(m.mk_eq(apply_subst(head_args.get(i), rule_subst), hvars.get(i)));
                }
            }

            for (unsigned i = 0; i < head_eargs.size(); ++i) {
                if (head_exp_constraint_needed[i]) {
                    unification_terms.push_back(m.mk_eq(apply_subst(head_eargs.get(i), rule_subst), hvalues.get(i)));
                }
            }

            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                expr_ref_vector body_eargs = ri->get_explicit_args(i, this);
                CASSERT("predabst", body_eargs.size() == bvalues.get(i).size());
                for (unsigned j = 0; j < body_eargs.size(); ++j) {
                    if (body_exp_constraint_needed[i][j]) {
                        unification_terms.push_back(m.mk_eq(apply_subst(body_eargs.get(j), rule_subst), bvalues.get(i).get(j)));
                    }
                }
            }

            return rule_subst;
        }

        // Returns a substitution vector mapping each variable used in r to a
        // fresh constant.
        expr_ref_vector get_subst_vect_free(rule* r, char const* prefix) const {
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

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) for template temp, which maps the head arguments to hvars
        // and the extra template parameters to their instantiated values.
        expr_ref_vector get_temp_subst_vect(template_info const* temp, expr_ref_vector const& hvars) const {
            return build_subst(temp->m_vars, vector_concat(hvars, m_template_param_values));
        }

        expr_ref_vector get_temp_subst_vect(template_info const* temp, var_ref_vector const& hvars) const {
            return build_subst(temp->m_vars, vector_concat(hvars.size(), (expr* const*)hvars.c_ptr(), m_template_param_values));
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) for template temp, which maps the head arguments to hvars
        // and the extra template parameters to their corresponding
        // uninterpreted constants.
        expr_ref_vector get_temp_subst_vect_noparams(template_info const* temp, expr_ref_vector const& hvars) const {
            return build_subst(temp->m_vars, vector_concat(hvars, m_template_params));
        }

        bool get_temp_application(app* a, expr_ref_vector const& rule_subst, expr_ref_vector& body, bool substitute_template_params = true) const {
            if (!m_func_decl2info.contains(a->get_decl())) {
                return false;
            }
            func_decl_info const* fi = m_func_decl2info[a->get_decl()];
            if (!fi->m_has_template) {
                return false;
            }
            template_info const* temp = fi->m_template;
            expr_ref_vector temp_args = apply_subst(expr_ref_vector(m, a->get_num_args(), a->get_args()), rule_subst);
            expr_ref_vector temp_subst(m);
            if (substitute_template_params) {
                temp_subst.swap(get_temp_subst_vect(temp, temp_args));
            }
            else {
                temp_subst.swap(get_temp_subst_vect_noparams(temp, temp_args));
            }
            body.append(apply_subst(temp->m_body, temp_subst));
            return true;
        }

        expr_ref_vector get_rule_body(rule_info const* ri, expr_ref_vector const& rule_subst, bool substitute_template_params = true) const {
            rule* r = ri->m_rule;
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref_vector body = apply_subst(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz), rule_subst);
            expr_ref_vector temp(m);
            if (get_temp_application(r->get_head(), rule_subst, temp, substitute_template_params)) {
                body.push_back(mk_not(mk_conj(temp)));
            }
            for (unsigned i = 0; i < usz; ++i) {
                expr_ref_vector temp(m);
                if (get_temp_application(r->get_tail(i), rule_subst, temp, substitute_template_params)) {
                    body.append(temp);
                }
            }
            return body;
        }

        expr_ref_vector get_rule_terms(rule_info const* ri, expr_ref_vector const& hargs, expr_ref_vector const& hvalues, vector<expr_ref_vector> const& bvalues, expr_ref_vector& rule_subst, bool substitute_template_params = true) const {
            CASSERT("predabst", rule_subst.empty());
            expr_ref_vector unification_terms(m);
            rule_subst.swap(get_subst_vect(ri, hargs, hvalues, bvalues, "s", unification_terms));
            expr_ref_vector body_terms = get_rule_body(ri, rule_subst, substitute_template_params);
            return vector_concat(unification_terms, body_terms);
        }

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

        expr_ref node_to_formula(node_info const* node) const {
            expr_ref_vector es(m);
			expr_ref_vector const& values = node->m_explicit_values;
			var_ref_vector const& args = node->m_fdecl_info->m_explicit_vars;
			CASSERT("predabst", values.size() == args.size());
			for (unsigned i = 0; i < values.size(); ++i) {
				es.push_back(m.mk_eq(args.get(i), values.get(i)));
			}
			cube_t const& cube = node->m_cube;
            expr_ref_vector const& preds = node->m_fdecl_info->m_preds;
            CASSERT("predabst", cube.size() == preds.size());
            for (unsigned i = 0; i < cube.size(); ++i) {
                if (cube[i]) {
                    es.push_back(preds[i]);
                }
            }
            return mk_conj(es);
        }

        void set_logic(smt::kernel& solver) const {
            if (m_fp_params.solver_logic().bare_str()) { // >>> does this make sense?
                bool result = solver.set_logic(m_fp_params.solver_logic());
                CASSERT("predabst", result);
            }
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
                if (is_regular_predicate(r->get_decl())) {
                    for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                        func_decl* fdecl = r->get_decl(j);
                        if (is_template_extra(fdecl)) {
                            STRACE("predabst", tout << "Error: found extra template constraint in non-head position\n";);
                            throw default_exception("found extra template constraint in non-head position");
                        }
                        if (is_template(fdecl)) {
                            STRACE("predabst", tout << "Error: found template " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found template " + fdecl->get_name().str() + " in non-head position");
                        }
                        if (is_explicit_arg_list(fdecl)) {
                            STRACE("predabst", tout << "Error: found explicit argument list " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found explicit argument list " + fdecl->get_name().str() + " in non-head position");
                        }
                        if (is_explicit_arg(fdecl)) {
                            STRACE("predabst", tout << "Error: found explicit argument " << fdecl->get_name() << " in body of regular rule\n";);
                            throw default_exception("found explicit argument " + fdecl->get_name().str() + " in body of regular rule");
                        }
                        if (is_predicate_list(fdecl)) {
                            STRACE("predabst", tout << "Error: found predicate list " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found predicate list " + fdecl->get_name().str() + " in non-head position");
                        }
                        if (is_arg_name_list(fdecl)) {
                            STRACE("predabst", tout << "Error: found argument name list " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found argument name list " + fdecl->get_name().str() + " in non-head position");
                        }
                        if (is_arg_name(fdecl)) {
                            STRACE("predabst", tout << "Error: found argument name " << fdecl->get_name() << " in body of regular rule\n";);
                            throw default_exception("found argument name " + fdecl->get_name().str() + " in body of regular rule");
                        }
                        process_func_decl(rules, fdecl);
                    }
                    process_func_decl(rules, r->get_decl());
                }
                else if (is_explicit_arg(r->get_decl())) {
                    STRACE("predabst", tout << "Error: found explicit argument " << r->get_decl()->get_name() << " in head position\n";);
                    throw default_exception("found explicit argument " + r->get_decl()->get_name().str() + " in head position");
                }
                else if (is_arg_name(r->get_decl())) {
                    STRACE("predabst", tout << "Error: found argument name " << r->get_decl()->get_name() << " in head position\n";);
                    throw default_exception("found argument name " + r->get_decl()->get_name().str() + " in head position");
                }
            }
        }

        void process_func_decl(rule_set const& rules, func_decl *fdecl) {
            CASSERT("predabst", is_regular_predicate(fdecl));
            CASSERT("predabst", fdecl->get_range() == m.mk_bool_sort());
            if (rules.is_output_predicate(fdecl)) {
                return;
            }

            if (!m_func_decl2info.contains(fdecl)) {
                bool is_dwf = is_dwf_predicate(fdecl);
                if (is_dwf) {
                    if (fdecl->get_arity() % 2 != 0) {
                        STRACE("predabst", tout << "Error: DWF predicate symbol " << fdecl->get_name() << " has arity " << fdecl->get_arity() << " which is odd\n";);
                        throw default_exception("DWF predicate symbol " + fdecl->get_name().str() + " has odd arity");
                    }
                    for (unsigned i = 0; i < fdecl->get_arity() / 2; ++i) {
                        unsigned j = fdecl->get_arity() / 2 + i;
                        if (fdecl->get_domain(i) != fdecl->get_domain(j)) {
                            STRACE("predabst", tout << "Error: DWF predicate symbol " << fdecl->get_name() << " has argument " << i << " of type " << mk_pp(fdecl->get_domain(i), m) << " and argument " << j << " of type " << mk_pp(fdecl->get_domain(j), m) << "\n";);
                            throw default_exception("DWF predicate symbol " + fdecl->get_name().str() + " has mismatching argument types");
                        }
                        // The following restriction may be removed in future.
                        if (fdecl->get_domain(i) != arith_util(m).mk_int()) {
                            STRACE("predabst", tout << "Error: DWF predicate symbol " << fdecl->get_name() << " has argument " << i << " of type " << mk_pp(fdecl->get_domain(i), m) << " which is not int\n";);
                            throw default_exception("DWF predicate symbol " + fdecl->get_name().str() + " has non-integer argument types");
                        }
                    }
                }

				var_ref_vector vars = get_arg_vars(fdecl);
				m_func_decls.push_back(alloc(func_decl_info, fdecl, vars, is_dwf));
                m_func_decl2info.insert(fdecl, m_func_decls.back());
                m_stats.m_num_predicate_symbols++;
                m_stats.m_num_predicate_symbol_arguments += fdecl->get_arity();
            }
        }

        bool is_dwf_predicate(func_decl const* pred) const {
            return pred->get_name().str().substr(0, 7) == "__dwf__";
        }

        void process_special_rules(rule_set& rules, bool(*p)(func_decl const*), void (imp::*f)(rule const*)) {
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
            CASSERT("predabst", r->get_decl()->get_range() == m.mk_bool_sort());

            if (m_template_params.size() > 0) {
                STRACE("predabst", tout << "Error: found multiple extra template constraints\n";);
                throw default_exception("found multiple extra template constraints");
            }

            var_ref_vector args(m);
            if (!args_are_distinct_vars(r->get_head(), args)) {
                STRACE("predabst", tout << "Error: extra template constraint has invalid argument list\n";);
                throw default_exception("extra template constraint has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: extra template constraint has an uninterpreted tail\n";);
                throw default_exception("extra template constraint has an uninterpreted tail");
            }

            // Replace the variables corresponding to the extra template parameters with fresh constants.
            expr_ref_vector extra_params = get_fresh_args(r->get_decl(), "b");
            expr_ref_vector extra_subst = build_subst(args, extra_params);
            expr_ref extras = apply_subst(mk_conj(expr_ref_vector(m, r->get_tail_size(), r->get_expr_tail())), extra_subst);
            STRACE("predabst", tout << "  " << mk_pp(extras, m) << "\n";);

            if (has_vars(extras)) {
                STRACE("predabst", tout << "Error: extra template constraint has free variables\n";);
                throw default_exception("extra template constraint has free variables");
            }

            CASSERT("predabst", m_template_params.empty());
            m_template_params.swap(extra_params);
            CASSERT("predabst", !m_template_extras);
            m_template_extras = extras;
            m_stats.m_num_template_params = m_template_params.size();
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
                STRACE("predabst", tout << "Error: found template for predicate symbol with zero-length name\n";);
                throw default_exception("found template for predicate symbol with zero-length name");
            }

            STRACE("predabst", tout << "Found template for predicate symbol " << suffix << "\n";);

            unsigned num_extras = m_template_params.size();
            if (head_decl->get_arity() < num_extras) {
                STRACE("predabst", tout << "Error: template has insufficient parameters for the extra template parameters\n";);
                throw default_exception("template for " + suffix.str() + " has insufficient parameters");
            }

            unsigned new_arity = head_decl->get_arity() - num_extras;
            for (unsigned i = 0; i < num_extras; ++i) {
                if (head_decl->get_domain(new_arity + i) != to_app(m_template_params.get(i))->get_decl()->get_range()) {
                    STRACE("predabst", tout << "Error: extra template parameter " << i << " is of wrong type\n";);
                    throw default_exception("extra parameter to template for " + suffix.str() + " is of wrong type");
                }
            }

            func_decl_ref suffix_decl(m.mk_func_decl(
                suffix,
                new_arity,
                head_decl->get_domain(),
                head_decl->get_range()), m);
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found template for non-existent predicate symbol\n";);
                throw default_exception("found template for non-existent predicate symbol " + suffix.str());
            }

            func_decl_info* fi = m_func_decl2info[suffix_decl];
            if (fi->m_is_dwf_predicate) {
                STRACE("predabst", tout << "Error: found template for DWF predicate symbol\n";);
                throw default_exception("found template for DWF predicate symbol " + suffix.str());
            }

            if (fi->m_has_template) {
                STRACE("predabst", tout << "Error: found multiple templates for " << suffix.str() << "\n";);
                throw default_exception("found multiple templates for " + suffix.str());
            }

            var_ref_vector args(m);
            if (!args_are_distinct_vars(r->get_head(), args)) {
                STRACE("predabst", tout << "Error: template has invalid argument list\n";);
                throw default_exception("template for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: template has an uninterpreted tail\n";);
                throw default_exception("template for " + suffix.str() + " has an uninterpreted tail");
            }

            var_ref_vector vars = get_arg_vars(r->get_decl());
            expr_ref_vector subst = build_subst(args, vars);
            expr_ref_vector body(m);
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                if (has_free_vars(r->get_tail(i), args)) {
                    STRACE("predabst", tout << "Error: template has free variables\n";);
                    throw default_exception("template for " + suffix.str() + " has free variables");
                }
                body.push_back(apply_subst(r->get_tail(i), subst));
            }
            STRACE("predabst", tout << "  " << suffix_decl->get_name() << "(" << vars << ") := " << body << "\n";);
            m_templates.push_back(alloc(template_info, vars, body));
            m_stats.m_num_templates++;

			fi->m_has_template = true;
			fi->m_template = m_templates.back();
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
                STRACE("predabst", tout << "Error: found explicit argument list for predicate symbol with zero-length name\n";);
                throw default_exception("found explicit argument list for predicate symbol with zero-length name");
            }

            STRACE("predabst", tout << "Found explicit argument list for predicate symbol " << suffix << "(" << expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()) << ")\n";);

            func_decl_ref suffix_decl(m.mk_func_decl(
                suffix,
                head_decl->get_arity(),
                head_decl->get_domain(),
                head_decl->get_range()), m);
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found explicit argument list for non-existent predicate symbol\n";);
                throw default_exception("found explicit argument list for non-existent predicate symbol " + suffix.str());
            }

            func_decl_info* fi = m_func_decl2info[suffix_decl];
            if (fi->m_has_template) {
                STRACE("predabst", tout << "Error: found explicit argument list for templated predicate symbol\n";);
                throw default_exception("found explicit argument list for templated predicate symbol " + suffix.str());
            }

            var_ref_vector args(m);
            if (!args_are_distinct_vars(r->get_head(), args)) {
                STRACE("predabst", tout << "Error: explicit argument list has invalid argument list\n";);
                throw default_exception("explicit argument list for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_tail_size() != r->get_uninterpreted_tail_size()) {
                STRACE("predabst", tout << "Error: explicit argument list has an interpreted tail\n";);
                throw default_exception("explicit argument list for " + suffix.str() + " has an interpreted tail");
            }

            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                app_ref tail(r->get_tail(i), m);
                if (!is_explicit_arg(tail->get_decl())) {
                    STRACE("predabst", tout << "Error: explicit argument list has unexpected predicate in uninterpreted tail\n";);
                    throw default_exception("explicit argument list for " + suffix.str() + " has unexpected predicate in uninterpreted tail");
                }
                CASSERT("predabst", tail->get_decl()->get_range() == m.mk_bool_sort());
                if (tail->get_decl()->get_arity() != 1) {
                    STRACE("predabst", tout << "Error: incorrect arity of __exparg__ predicate\n";);
                    throw default_exception("explicit argument list for " + suffix.str() + " has __exparg__ predicate of incorrect arity");
                }
                if (!is_var(tail->get_arg(0))) {
                    STRACE("predabst", tout << "Error: non-variable argument to __exparg__ predicate\n";);
                    throw default_exception("explicit argument list for " + suffix.str() + " has __exparg__ predicate with non-variable argument");
                }
                var_ref v(to_var(tail->get_arg(0)), m);
                if (!args.contains(v)) {
                    STRACE("predabst", tout << "Error: argument to __exparg__ predicate does not appear in the head\n";);
                    throw default_exception("explicit argument list for " + suffix.str() + " has __exparg__ predicate with argument that does not appear in the head");
                }
                unsigned j = vector_find(args, v.get());
                if (fi->m_explicit_args.get(j)) {
                    STRACE("predabst", tout << "Error: duplicate __exparg__ declaration for argument " << j << "\n";);
                    throw default_exception("explicit argument list for " + suffix.str() + " has duplicate __exparg__ declaration for argument");
                }
                m_stats.m_num_explicit_arguments++;
                if (m_fp_params.use_exp_eval()) {
                    STRACE("predabst", tout << "Found explicit argument declaration for argument " << j << "\n";);
                    fi->m_explicit_args[j] = true;
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
                STRACE("predabst", tout << "Error: found argument name list for predicate symbol with zero-length name\n";);
                throw default_exception("found argument name list for predicate symbol with zero-length name");
            }

            STRACE("predabst", tout << "Found argument name list for predicate symbol " << suffix << "(" << expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()) << ")\n";);

            func_decl_ref suffix_decl(m.mk_func_decl(
                suffix,
                head_decl->get_arity(),
                head_decl->get_domain(),
                head_decl->get_range()), m);
            if (!m_func_decl2info.contains(suffix_decl)) {
                STRACE("predabst", tout << "Error: found argument name list for non-existent predicate symbol\n";);
                throw default_exception("found argument name list for non-existent predicate symbol " + suffix.str());
            }

            func_decl_info* fi = m_func_decl2info[suffix_decl];
            if (fi->m_has_template) {
                STRACE("predabst", tout << "Error: found argument name list for templated predicate symbol\n";);
                throw default_exception("found argument name list for templated predicate symbol " + suffix.str());
            }

            var_ref_vector args(m);
            if (!args_are_distinct_vars(r->get_head(), args)) {
                STRACE("predabst", tout << "Error: argument name list has invalid argument list\n";);
                throw default_exception("argument name list for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_tail_size() != r->get_uninterpreted_tail_size()) {
                STRACE("predabst", tout << "Error: argument name list has an interpreted tail\n";);
                throw default_exception("argument name list for " + suffix.str() + " has an interpreted tail");
            }

            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                app_ref tail(r->get_tail(i), m);
                if (!is_arg_name(tail->get_decl())) {
                    STRACE("predabst", tout << "Error: argument name list has unexpected predicate in uninterpreted tail\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has unexpected predicate in uninterpreted tail");
                }
                CASSERT("predabst", tail->get_decl()->get_range() == m.mk_bool_sort());
                if (tail->get_decl()->get_arity() != 1) {
                    STRACE("predabst", tout << "Error: incorrect arity of __name__X predicate\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has __name__X predicate of incorrect arity");
                }
                if (!is_var(tail->get_arg(0))) {
                    STRACE("predabst", tout << "Error: non-variable argument to __name__X predicate\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has __name__X predicate with non-variable argument");
                }
                var_ref v(to_var(tail->get_arg(0)), m);
                if (!args.contains(v)) {
                    STRACE("predabst", tout << "Error: argument to __name__X predicate does not appear in the head\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has __name__X predicate with argument that does not appear in the head");
                }
                unsigned j = vector_find(args, v.get());
                if (fi->m_var_names.get(j)) {
                    STRACE("predabst", tout << "Error: duplicate name for argument " << j << "\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has duplicate name for argument");
                }
                symbol name(tail->get_decl()->get_name().str().substr(8).c_str());
                if (name.str().empty()) {
                    STRACE("predabst", tout << "Error: zero-length name for argument " << j << "\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has zero-length name for argument");
                }
                func_decl_ref name_decl(m.mk_const_decl(name, args.get(j)->get_sort()), m);
                if (fi->m_var_names.contains(name_decl)) {
                    STRACE("predabst", tout << "Error: non-unique name for argument " << j << "\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has non-unique argument names");
                }
                if (fi->m_var_names.contains(name_decl)) {
                    STRACE("predabst", tout << "Error: non-unique name for argument " << j << "\n";);
                    throw default_exception("argument name list for " + suffix.str() + " has non-unique argument names");
                }
                m_stats.m_num_named_arguments++;
                if (fi->m_explicit_args.get(j)) {
                    STRACE("predabst", tout << "Ignoring name for explicit argument " << j << "\n";);
                }
                else {
                    STRACE("predabst", tout << "Found name " << name << " for argument " << j << "\n";);
                    fi->m_var_names[j] = name_decl;
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
				STRACE("predabst", tout << "Error: found predicate list for predicate symbol with zero-length name\n";);
				throw default_exception("found predicate list for predicate symbol with zero-length name");
			}

			STRACE("predabst", tout << "Found predicate list for predicate symbol " << suffix << "(" << expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()) << ")\n";);

			func_decl_ref suffix_decl(m.mk_func_decl(
				suffix,
				head_decl->get_arity(),
				head_decl->get_domain(),
				head_decl->get_range()), m);
			if (!m_func_decl2info.contains(suffix_decl)) {
				STRACE("predabst", tout << "Error: found predicate list for non-existent predicate symbol\n";);
				throw default_exception("found predicate list for non-existent predicate symbol " + suffix.str());
			}

			func_decl_info* fi = m_func_decl2info[suffix_decl];
			if (fi->m_has_template) {
				STRACE("predabst", tout << "Error: found predicate list for templated predicate symbol\n";);
				throw default_exception("found predicate list for templated predicate symbol " + suffix.str());
			}

			var_ref_vector args(m);
			if (!args_are_distinct_vars(r->get_head(), args)) {
				STRACE("predabst", tout << "Error: predicate list has invalid argument list\n";);
				throw default_exception("predicate list for " + suffix.str() + " has invalid argument list");
			}

			var_ref_vector non_explicit_args(m);
			for (unsigned i = 0; i < args.size(); ++i) {
				if (!fi->m_explicit_args.get(i)) {
					non_explicit_args.push_back(args.get(i));
				}
			}

			if (r->get_uninterpreted_tail_size() != 0) {
				STRACE("predabst", tout << "Error: predicate list has an uninterpreted tail\n";);
				throw default_exception("predicate list for " + suffix.str() + " has an uninterpreted tail");
			}

			// Add p1..pN to m_func_decl2info[SUFFIX].m_preds.
			expr_ref_vector subst = build_subst(args, fi->m_vars); // >>> this ought to be neater
			for (unsigned i = 0; i < r->get_tail_size(); ++i) {
				if (has_free_vars(r->get_tail(i), args)) {
					STRACE("predabst", tout << "Error: predicate has free variables\n";);
					throw default_exception("predicate for " + suffix.str() + " has free variables");
				}
				if (has_free_vars(r->get_tail(i), non_explicit_args)) {
					STRACE("predabst", tout << "Error: predicate uses explicit arguments\n";);
					throw default_exception("predicate for " + suffix.str() + " uses explicit arguments");
				}

				expr_ref pred = apply_subst(to_expr(r->get_tail(i)), subst);
				STRACE("predabst", tout << "  predicate " << i << ": " << mk_pp(pred, m) << "\n";);
				m_stats.m_num_initial_predicates++;
				maybe_add_pred(fi, pred);
			}
		}

        lbool abstract_check_refine() {
            STRACE("predabst", print_initial_state(tout););

            if (!instantiate_templates()) {
                STRACE("predabst", tout << "Initial template refinement unsuccessful: result is UNSAT\n";);
                return l_true;
            }

            for (unsigned i = 0; i < m_rules.size(); ++i) {
                rule_info* ri = m_rules[i];
                instantiate_rule(ri);
                ri->m_unsat = !rule_body_satisfiable(ri);
            }

            // The only things that change on subsequent iterations of this loop are
            // the predicate lists
            // (m_func_decl2info::m_preds) and template instances.  The latter can have an
            // effect on the execution of the algorithm via the initial nodes
            // set up by initialize_abs.
            unsigned refine_count = 0;
            while (true) {
                m_stats.m_num_refinement_iterations++;
				for (unsigned i = 0; i < m_nodes.size(); ++i) {
					dealloc(m_nodes[i]);
				}
                m_nodes.reset();
                for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                    func_decl_info* fi = m_func_decls.get(i);
                    if (!fi->m_has_template) {
                        fi->m_max_reach_nodes.reset();
                    }
                }

                // Set up m_rules for this iteration:
                // for each rule: ground body and instantiate predicates for applications
                for (unsigned i = 0; i < m_rules.size(); ++i) {
                    rule_info* ri = m_rules[i];
                    instantiate_rule_preds(ri);
                }

                STRACE("predabst", print_refinement_state(tout, refine_count););

                for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                    func_decl_info* fi = m_func_decls[i];
                    fi->m_new_preds = 0;
                }

                acr_error error;
                if (find_solution(refine_count, error)) {
                    STRACE("predabst", tout << "Solution found: result is SAT\n";);
                    return l_false;
                }
                else if (!m_fp_params.use_refinement()) {
                    STRACE("predabst", tout << "No solution found: result is UNSAT\n";);
                    return l_true;
                }
                else {
                    // Our attempt to find a solution failed and we want to try refinement.
                    core_tree_info core_info;
                    core_tree_wf_info core_info_wf(m);
                    core_tree_template_info core_info_template(m);
                    node_info const* error_node = error.m_node;
                    expr_ref_vector error_args = get_fresh_args(error_node->m_fdecl_info, "r");
                    if (not_reachable_without_abstraction(error_node, error_args, core_info)) {
                        // The problem node isn't reachable without abstraction.
                        // We need to refine the abstraction and retry.
                        if (!refine_predicates_not_reachable(error_node, error_args, core_info)) {
                            STRACE("predabst", tout << "Predicate refinement unsuccessful: result is UNKNOWN\n";);
                            return l_undef;
                        }

                        STRACE("predabst", tout << "Predicate refinement successful: retrying\n";);
                    }
                    else if ((error.m_kind == not_wf) && wf_without_abstraction(error_node, error_args, core_info_wf)) {
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
                        constrain_templates(error_node, error_args, error.m_kind);
                        if (!instantiate_templates()) {
                            STRACE("predabst", tout << "Template refinement unsuccessful: result is UNSAT\n";);
                            return l_true;
                        }

                        STRACE("predabst", tout << "Template refinement successful: retrying\n";);

                        for (unsigned i = 0; i < m_rules.size(); ++i) {
                            rule_info* ri = m_rules[i];
                            instantiate_rule(ri);
                            ri->m_unsat = !rule_body_satisfiable(ri);
                        }

                        for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                            func_decl_info* fi = m_func_decls[i];
                            fi->m_new_preds = fi->m_preds.size();
                        }
                    }
                }

                refine_count++;
            }
        }

        void invert(expr_ref_vector& exprs) {
            for (unsigned i = 0; i < exprs.size(); ++i) {
                exprs[i] = m.mk_not(exprs.get(i));
            }
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

        void instantiate_rule(rule_info* ri) {
            STRACE("predabst", tout << "Instantiating rule " << ri << "\n";);
            rule_instance_info& info = ri->m_instance_info;
            info.reset();

            // create ground body (including templated head/body applications)
            expr_ref_vector body = get_rule_body(ri, ri->m_rule_subst);
            pre_simplify(body);
            info.m_body.swap(body);

            // instantiate explicit arguments to non-templated head applications
            func_decl_info const* fi = ri->get_decl(this);
            if (fi) {
                CASSERT("predabst", !fi->m_has_template);
                expr_ref_vector head_args = apply_subst(ri->get_explicit_args(this), ri->m_rule_subst);
                pre_simplify(head_args);
                // >>> share code
                vector<bool> known_args;
                for (unsigned i = 0; i < head_args.size(); ++i) {
                    bool known = get_all_vars(expr_ref(head_args.get(i), m)).empty();
                    known_args.push_back(known);
                    if (known) {
                        m_stats.m_num_known_explicit_arguments++;
                    }
                }
                info.m_head_explicit_args.swap(head_args);
                info.m_head_known_args.swap(known_args);
            }

            info.m_num_head_unknown_args = 0;
            for (unsigned i = 0; i < info.m_head_known_args.size(); ++i) {
                if (!info.m_head_known_args.get(i)) {
                    ++info.m_num_head_unknown_args;
                }
            }

            // instantiate explicit arguments to non-templated body applications
            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                func_decl_info const* fi = ri->get_decl(i, this);
                CASSERT("predabst", fi && !fi->m_has_template);
                expr_ref_vector body_args = apply_subst(ri->get_explicit_args(i, this), ri->m_rule_subst);
                pre_simplify(body_args);
                vector<bool> known_args;
                for (unsigned j = 0; j < body_args.size(); ++j) {
                    bool known = get_all_vars(expr_ref(body_args.get(j), m)).empty();
                    known_args.push_back(known);
                    if (known) {
                        m_stats.m_num_known_explicit_arguments++;
                    }
                }
                info.m_body_explicit_args.push_back(body_args);
                info.m_body_known_args.push_back(known_args);
            }

            // create placeholders for non-templated body applications
            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                info.m_body_preds.push_back(expr_ref_vector(m));
            }

#ifdef PREDABST_SOLVER_PER_RULE
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                solver_for(ri)->assert_expr(info.m_body.get(i));
            }
#endif
        }

        void instantiate_rule_preds(rule_info* ri) {
            STRACE("predabst", tout << "Instantiating predicates for rule " << ri << "\n";);
            rule_instance_info& info = ri->m_instance_info;

#ifndef PREDABST_SOLVER_PER_RULE
            scoped_push push(m_solver);
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_solver.assert_expr(info.m_body.get(i));
            }
#endif

            // create instantiations for non-templated head applications
            func_decl_info const* fi = ri->get_decl(this);
            if (fi) {
                CASSERT("predabst", !fi->m_has_template);
                expr_ref_vector head_args = apply_subst(ri->get_non_explicit_args(this), ri->m_rule_subst);
                expr_ref_vector head_preds = app_inst_preds(fi, head_args);
                invert(head_preds);
                pre_simplify(head_preds);
                if (m_fp_params.convert_true_head_preds()) {
                    maybe_make_true(head_preds, solver_for(ri));
                }
                if (m_fp_params.convert_false_head_preds()) {
                    maybe_make_false(head_preds, solver_for(ri));
                }
#ifdef PREDABST_SOLVER_PER_RULE
                assert_guarded_exprs(head_preds, solver_for(ri));
#endif
                info.m_head_preds.append(head_preds);
                m_stats.m_num_head_predicates += head_preds.size();
            }

            // create instantiations for non-templated body applications
            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                func_decl_info const* fi = ri->get_decl(i, this);
                CASSERT("predabst", fi && !fi->m_has_template);
                expr_ref_vector body_args = apply_subst(ri->get_non_explicit_args(i, this), ri->m_rule_subst);
                expr_ref_vector body_preds = app_inst_preds(fi, body_args);
                pre_simplify(body_preds);
                if (m_fp_params.convert_true_body_preds()) {
                    maybe_make_true(body_preds, solver_for(ri));
                }
                if (m_fp_params.convert_false_body_preds()) {
                    maybe_make_false(body_preds, solver_for(ri));
                }
#ifdef PREDABST_SOLVER_PER_RULE
                assert_guarded_exprs(body_preds, solver_for(ri));
#endif
                info.m_body_preds.get(i).append(body_preds);
                m_stats.m_num_body_predicates += body_preds.size();
            }
        }

        // instantiate each predicate by replacing its free variables with (grounded) arguments of gappl
        expr_ref_vector app_inst_preds(func_decl_info const* fi, expr_ref_vector const& args) {
            // instantiation maps preds variables to head arguments
            expr_ref_vector inst = build_subst(fi->m_non_explicit_vars, args);
            // preds instantiates to inst_preds
            return apply_subst(expr_ref_vector(m, fi->m_new_preds, fi->m_preds.c_ptr() + (fi->m_preds.size() - fi->m_new_preds)), inst);
        }

        void assert_guarded_exprs(expr_ref_vector& exprs, smt::kernel* solver) const {
            expr_ref_vector guard_vars(m);
            for (unsigned i = 0; i < exprs.size(); ++i) {
                if (!m.is_false(exprs.get(i)) && !m.is_true(exprs.get(i))) {
                    expr_ref g(m.mk_fresh_const("g", m.mk_bool_sort()), m);
                    expr_ref e(m.mk_iff(exprs.get(i), g), m);
                    STRACE("predabst", tout << "Asserting " << mk_pp(e, m) << "\n";);
                    solver->assert_expr(e);
                    exprs[i] = g;
                }
            }
        }

        bool rule_body_satisfiable(rule_info const* ri) {
            rule_instance_info const& info = ri->m_instance_info;

#ifndef PREDABST_SOLVER_PER_RULE
            scoped_push _push1(m_solver);
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_solver.assert_expr(info.m_body[i]);
            }
#endif

			lbool result = check(solver_for(ri));
            if (result == l_false) {
                // unsat body
                STRACE("predabst", tout << "Rule " << ri << " will always fail\n";);
                m_stats.m_num_rules_unsatisfiable++;
                return false;
            }
            else {
                return true;
            }
        }

        expr_ref model_eval_app(model_ref const& md, app const* app) {
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
            return apply_subst(exp, subst);
        }

        expr_ref ground(expr_ref const& exp, char const* prefix) {
            ptr_vector<sort> sorts;
            get_free_vars(exp, sorts);
            expr_ref_vector subst(m);
            subst.reserve(sorts.size());
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (sorts[i]) {
                    subst[i] = m.mk_fresh_const(prefix, sorts[i]);
                }
            }
            return apply_subst(exp, subst);
        }

        bool check_solution() {
            smt_params new_param;
            smt::kernel solver(m, new_param);
            set_logic(solver);
            model_ref md = get_model();
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                rule* r = m_rules[i]->m_rule;
                unsigned usz = r->get_uninterpreted_tail_size();
                unsigned tsz = r->get_tail_size();
                expr_ref_vector body_exp_terms(m, tsz - usz, r->get_expr_tail() + usz);
                for (unsigned j = 0; j < usz; ++j) {
                    body_exp_terms.push_back(model_eval_app(md, r->get_tail(j)));
                }
                expr_ref body_exp = mk_conj(body_exp_terms);
                expr_ref head_exp(m);
                if (m_func_decl2info.contains(r->get_decl())) {
                    head_exp = model_eval_app(md, r->get_head());
                }
                else {
                    head_exp = m.mk_false();
                }

                scoped_push push(solver);
                solver.assert_expr(ground(expr_ref(m.mk_and(body_exp, mk_not(head_exp)), m), "c"));
                if (check(&solver) != l_false) {
                    STRACE("predabst", tout << "Solution does not satisfy rule " << i << "\n";);
                    return false;
                }
            }
            return true;
        }

        bool find_solution(unsigned refine_count, acr_error& error) {
            m_node_worklist.reset();

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

//#ifdef Z3DEBUG
                if (!check_solution()) {
                    throw default_exception("check_solution failed");
                }
//#endif

                // We managed to find a solution.
                return true;
            }
            catch (acr_error const& error2) {
                // We failed to find a solution.
                error = error2;
                return false;
            }
        }

        void initialize_abs(rule_info const* ri) {
            cart_pred_abst_rule(ri);
        }

        void inference_step(node_info const* node) {
            // Find all rules whose body contains the func_decl of the new node.
            func_decl_info const* fi = node->m_fdecl_info;
            rule_vector const& rules = fi->m_users;
            STRACE("predabst", tout << "Performing inference from node " << node << " using rules " << rules << "\n";);
            for (rule_vector::const_iterator r_it = rules.begin(); r_it != rules.end(); ++r_it) {
				rule_info const* ri = *r_it;
                STRACE("predabst-cprod", tout << "Attempting to apply rule " << ri << "\n";);
                // Find all positions in the body of this rule at which the
                // func_decl appears.
                uint_set positions = get_rule_body_positions(ri, fi);
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

        uint_set get_rule_body_positions(rule_info const* ri, func_decl_info const* fi) {
            uint_set positions;
            for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                if (ri->get_decl(i, this) == fi) {
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
            rule_instance_info const& info = ri->m_instance_info;
            CASSERT("predabst", (fixed_node == NULL) || (fixed_pos < ri->get_tail_size()));

            if (ri->m_unsat) {
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
                node_vector const& nodes = (i == fixed_pos) ? singleton_set(fixed_node) : ri->get_decl(i, this)->m_max_reach_nodes;
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
                    expr_ref_vector const& body_preds = info.m_body_preds[i];
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
                        expr_ref_vector const& values = node->m_explicit_values;
                        expr_ref_vector const& body_args = info.m_body_explicit_args[i];
                        vector<bool> const& known_args = info.m_body_known_args[i];
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
                    expr_ref_vector const& body_preds = info.m_body_preds[i];
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
                    expr_ref_vector const& values = node->m_explicit_values;
                    expr_ref_vector const& body_args = info.m_body_explicit_args[i];
                    vector<bool> const& known_args = info.m_body_known_args[i];
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

			// This push is unnecessary if (defined(PREDABST_SOLVER_PER_RULE) && !defined(PREDABST_USE_ALLSAT)).
            scoped_push _push1(*solver_for(ri));

#ifndef PREDABST_SOLVER_PER_RULE
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_solver.assert_expr(info.m_body[i]);
            }
#endif

			expr_ref_vector head_es = info.m_head_preds;
#if !defined(PREDABST_SOLVER_PER_RULE)
			if (m_fp_params.use_head_assumptions()) {
				assert_guarded_exprs(head_es, solver_for(ri));
			}
#endif

#if !defined(PREDABST_SOLVER_PER_RULE)
			// >>> move to query()
			if (m_fp_params.use_body_assumptions() && !m_fp_params.summarize_cubes()) {
				STRACE("predabst", tout << "Can't use body assumptions without having guard variables to assume\n";);
				throw default_exception("can't use body assumptions without having guard variables to assume");
			}
#endif

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
					STRACE("predabst", tout << "  " << mk_pp(to_assert, m) << "\n";);
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
            rule_instance_info const& info = ri->m_instance_info;
            unsigned num_preds = es.size();
            CASSERT("predabst", (!ri->get_decl(this) && (num_preds == 0)) || (num_preds == ri->get_decl(this)->m_preds.size()));
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
            rule_instance_info const& info = ri->m_instance_info;
            expr_ref_vector values(m);
            if (info.m_head_explicit_args.size() == 0) {
                // nothing to do
            }
            else if (m_fp_params.skip_known_head_values() && (info.m_num_head_unknown_args == 0)) {
                values.append(info.m_head_explicit_args);
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
                for (unsigned i = 0; i < info.m_head_explicit_args.size(); ++i) {
                    if (m_fp_params.skip_known_head_values() && info.m_head_known_args.get(i)) {
                        values.push_back(info.m_head_explicit_args.get(i));
                    }
                    else {
                        expr_ref val(m);
                        try {
                            ev(info.m_head_explicit_args.get(i), val);
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
            for (unsigned i = 0; i < info.m_head_explicit_args.size(); ++i) {
                if (!info.m_head_known_args.get(i)) {
                    es.push_back(m.mk_eq(info.m_head_explicit_args.get(i), values.get(i)));
                }
            }
            expr_ref to_assert(m.mk_not(mk_conj(es)), m);
			pre_simplify(to_assert);
            solver_for(ri)->assert_expr(to_assert);
            lbool result = check(solver_for(ri), assumptions.size(), assumptions.c_ptr());
			if (result == l_true) {
                STRACE("predabst", tout << "Error: values of explicit arguments were not uniquely determined\n";);
                throw default_exception("values of explicit arguments for " + ri->get_decl(this)->m_fdecl->get_name().str() + " were not uniquely determined");
            }
#endif
            return values;
        }

        void check_node_property(node_info const* node) {
            if (!node->m_fdecl_info) {
                STRACE("predabst", tout << "Reached query symbol " << node->m_fdecl_info << "\n";);
                throw acr_error(node, reached_query);
            }
            CASSERT("predabst", !node->m_fdecl_info->m_has_template);
            if (node->m_fdecl_info->m_is_dwf_predicate) {
                if (!is_well_founded(node)) {
                    STRACE("predabst", tout << "Formula is not well-founded\n";);
                    throw acr_error(node, not_wf);
                }
                m_stats.m_num_well_founded_nodes++;
            }
        }

        bool is_well_founded(node_info const* node) {
            func_decl_info const* fi = node->m_fdecl_info;
            CASSERT("predabst", fi->m_is_dwf_predicate);

            CASSERT("predabst", node->m_explicit_values.size() % 2 == 0);
            unsigned n = node->m_explicit_values.size() / 2;
            for (unsigned i = 0; i < n; ++i) {
                if (node->m_explicit_values[i] != node->m_explicit_values[i + n]) {
                    return true;
                }
            }

            expr_ref expr = cube_to_formula(node->m_cube, fi->m_preds);
            expr_ref_vector args = get_fresh_args(fi, "s");
            expr_ref to_rank = apply_subst(expr, build_subst(fi->m_non_explicit_vars, args));

            return well_founded(args, to_rank, NULL, NULL);
        }

        node_info const* add_node(rule_info const* ri, cube_t const& cube, expr_ref_vector const& values, node_vector const& nodes = node_vector()) {
            CASSERT("predabst", cube.size() == ri->m_instance_info.m_head_preds.size());
            CASSERT("predabst", values.size() == ri->m_instance_info.m_head_explicit_args.size());
            m_stats.m_num_nodes_discovered++;
            func_decl_info* fi = ri->get_decl(this);
            if (fi) {
                // first fixpoint check combined with maximality maintainance
                node_vector old_lt_nodes;
                for (node_vector::const_iterator it = fi->m_max_reach_nodes.begin(); it != fi->m_max_reach_nodes.end(); ++it) {
                    if (!vector_equals(values, (*it)->m_explicit_values)) {
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
                    fi->m_max_reach_nodes.erase(*it);
                    m_stats.m_num_frontier_nodes_removed++;
                    if (m_node_worklist.contains(*it)) {
                        m_node_worklist.erase(*it); // removing non-existent element is ok
                        m_stats.m_num_nodes_discarded++;
                    }
                }
            }
            // no fixpoint reached hence create new node
            m_nodes.push_back(alloc(node_info, m_nodes.size(), fi, cube, values, ri, nodes));
            node_info const* node = m_nodes.back();
            if (fi) {
                fi->m_max_reach_nodes.insert(node);
                m_stats.m_num_frontier_nodes_added++;
            }
            m_node_worklist.insert(node);
            m_stats.m_num_nodes_enqueued++;
            STRACE("predabst", tout << "Added node " << node << " for " << fi << "\n";);
            return node;
        }

        bool not_reachable_without_abstraction(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info& core_info) const {
            STRACE("predabst", tout << "Determining reachability of node " << root_node << " without abstraction\n";);
            bool result = mk_core_tree(root_node, root_args, core_info);
            STRACE("predabst", tout << "Node " << root_node << " is " << (result ? "not " : "") << "reachable without abstraction\n";);
            return result;
        }

        bool refine_predicates_not_reachable(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info const& core_info) {
            vector<func_decl_info*> name2func_decl;
            expr_ref last_clause_body(m);
            core_clauses clauses = mk_core_clauses(root_node, root_args, core_info, name2func_decl, &last_clause_body);
            core_clauses clauses2 = cone_of_influence(clauses, last_clause_body);
            core_clause_solutions solutions = solve_core_clauses(clauses2);
            return refine_preds(solutions, name2func_decl);
        }

        bool wf_without_abstraction(node_info const* root_node, expr_ref_vector const& root_args, core_tree_wf_info& core_wf_info) const {
            STRACE("predabst", tout << "Determining well-foundedness of node " << root_node << " without abstraction\n";);
            CASSERT("predabst", root_node->m_fdecl_info->m_is_dwf_predicate);
            expr_ref actual_cube = mk_leaves(root_node, root_args);
            quantifier_elimination(root_args, actual_cube);
            bool result = well_founded(root_args, actual_cube, &core_wf_info.m_bound, &core_wf_info.m_decrease);
            STRACE("predabst", tout << "Node " << root_node << " is " << (result ? "" : "not ") << "well-founded without abstraction\n";);
            return result;
        }

        bool refine_predicates_wf(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info const& core_info, core_tree_wf_info const& core_wf_info) {
            vector<func_decl_info*> name2func_decl;
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

        bool refine_preds(core_clause_solutions const& solutions, vector<func_decl_info*> const& name2func_decl) {
            unsigned new_preds_added = 0;
            for (unsigned i = 0; i < solutions.size(); ++i) {
                core_clause_solution const& solution = solutions.get(i);
                CASSERT("predabst", solution.m_head.m_name < name2func_decl.size());
                func_decl_info* fi = name2func_decl[solution.m_head.m_name];
                CASSERT("predabst", fi && !fi->m_has_template);
                expr_ref pred(replace_pred(solution.m_head.m_args, fi->m_non_explicit_vars, solution.m_body), m);
                new_preds_added += maybe_add_pred(fi, pred);
            }
            return (new_preds_added > 0);
        }

        unsigned maybe_add_pred(func_decl_info* fi, expr_ref const& p) {
            expr_ref pred = normalize_pred(p, fi->m_non_explicit_vars);
            if (m.is_true(pred) || m.is_false(pred)) {
                STRACE("predabst", tout << "Ignoring predicate " << mk_pp(pred, m) << " for " << fi << "\n";);
                return 0;
            }
            else if (fi->m_preds.contains(pred)) {
                STRACE("predabst", tout << "Predicate " << mk_pp(pred, m) << " for " << fi << " is already present\n";);
                return 0;
            }
            else {
                unsigned new_preds_added = 1;
                add_pred(fi, pred);
                m_stats.m_num_predicates_added++;
                if (m_fp_params.use_query_naming() && new_preds_added) {
                    var_ref_vector used_vars = to_vars(get_all_vars(pred));
                    func_decl_ref_vector used_var_names(m);
                    for (unsigned i = 0; i < used_vars.size(); ++i) {
                        CASSERT("predabst", is_var(used_vars.get(i)));
                        unsigned j = used_vars.get(i)->get_idx();
                        if (!fi->m_var_names.get(j)) {
                            STRACE("predabst", tout << "Don't have name for variable " << mk_pp(used_vars.get(i), m) << " used in predicate " << mk_pp(p, m) << " for " << fi << "\n";);
                            return new_preds_added;
                        }
                        used_var_names.push_back(fi->m_var_names.get(j));
                    }
                    for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                        func_decl_info* fi2 = m_func_decls[i];
                        if (fi2 == fi) {
                            continue;
                        }
                        if (is_subset(used_var_names, fi2->m_var_names)) {
                            var_ref_vector used_vars2(m);
                            for (unsigned j = 0; j < used_var_names.size(); ++j) {
                                unsigned k = vector_find(fi2->m_var_names, used_var_names.get(j));
                                used_vars2.push_back(fi2->m_vars.get(k));
                            }
                            new_preds_added++;
                            add_pred(fi2, apply_subst(pred, build_subst(used_vars, used_vars2)));
                            m_stats.m_num_predicates_added_query_naming++;
                        }
                    }
                }
                return new_preds_added;
            }
        }

        void add_pred(func_decl_info* fi, expr_ref const& pred) {
            CASSERT("predabst", !fi->m_preds.contains(pred));
            CASSERT("predabst", vector_intersection(fi->m_explicit_vars, to_vars(get_all_vars(pred))).empty());
            STRACE("predabst", tout << "Found new predicate " << mk_pp(pred, m) << " for " << fi << "\n";);
            fi->m_preds.push_back(pred);
            fi->m_new_preds++;
        }

        void constrain_templates(node_info const* error_node, expr_ref_vector const& error_args, acr_error_kind error_kind) {
            expr_ref cs = mk_leaves(error_node, error_args, false);
            quantifier_elimination(vector_concat(error_args, m_template_params), cs);

            expr_ref to_solve(m);
            if (error_kind == reached_query) {
                STRACE("predabst", tout << "Refining templates (reached query)\n";);
                to_solve = template_constraint_reached_query(cs);
            }
            else {
                CASSERT("predabst", error_kind == not_wf);
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

        expr_ref template_constraint_reached_query(expr_ref cs) {
            return expr_ref(m.mk_not(cs), m);
        }

        expr_ref template_constraint_not_wf(expr_ref_vector const& args, expr_ref cs) {
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
			if (m_fp_params.no_simplify()) {
				new_param.m_preprocess = false;
			}
            smt::kernel solver(m, new_param);
            set_logic(solver);

            expr_ref_vector terms = get_conj_terms(mk_leaves(root_node, root_args));
            pre_simplify(terms);

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
					tout << "Example model, assuming guard_vars " << guard_vars << ":\n";
					model_ref modref;
                    solver.get_model(modref);
					CASSERT("predabst", modref);
					for (unsigned i = 0; i < modref->get_num_constants(); ++i) {
						func_decl_ref c(modref->get_constant(i), m);
						expr_ref e(modref->get_const_interp(c), m);
						tout << "  " << c->get_name() << " has value " << mk_pp(e, m) << "\n";
					}
				});
                return false;
            }
            else {
                return true;
            }
        }

        core_clauses mk_core_clauses(node_info const* root_node, expr_ref_vector const& root_args, core_tree_info const& core_info, vector<func_decl_info*>& name2func_decl, expr_ref* last_clause_body = NULL) const {
            STRACE("predabst", tout << "Building clauses from " << core_info.m_count << " assertions\n";);
            core_clauses clauses;

            unsigned last_count = core_info.m_count;
            unsigned count = 0;

            vector<name_app> todo;
            vector<node_info const*> name2node;
            name2node.push_back(root_node);
            name2func_decl.push_back(root_node->m_fdecl_info);
            todo.push_back(name_app(0, root_args));

            while (!todo.empty()) {
                name_app item = todo.back();
                todo.pop_back();

                expr_ref_vector cs(m);
                vector<name_app> parents;

                node_info const* node = name2node[item.m_name];
                rule_info const* ri = node->m_parent_rule;

                if (count < last_count) {
                    expr_ref_vector const& hvalues = node->m_explicit_values;
                    vector<expr_ref_vector> bvalues;
                    for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                        node_info const* qnode = node->m_parent_nodes[i];
                        bvalues.push_back(qnode->m_explicit_values);
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
                            expr_ref_vector pargs = apply_subst(ri->get_non_explicit_args(i, this), rule_subst);
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
                            name2func_decl.push_back(qnode->m_fdecl_info);
                            todo.push_back(name_app(qname, qargs));
                            parents.push_back(name_app(qname, qargs));
                        }
                    }
                }

                core_clause clause(item, cs, parents);
                STRACE("predabst", tout << "Adding clause for " << node->m_fdecl_info << ": " << clause << "\n";);
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

            STRACE("predabst", tout << "Computing cone of influence for expression " << mk_pp(critical, m) << "\n";);
                
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
                    tout << "  " << mk_pp(it->m_key, m) << " -> component " << it->m_value << "\n";
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
            expr_ref_vector assertions(m);
            vector<unsigned> assertion_start_index;
            for (unsigned i = 0; i < clauses.size(); ++i) {
                assertion_start_index.push_back(assertions.size());
                core_clause const& clause = clauses[i];
                for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
                    assertions.push_back(to_nnf(expr_ref(clause.m_interp_body[j], m))); // >>> to_nnf is a bit of a hack here (why?)
                }
            }

            vector<int64> assertion_coeffs;
            bool result = get_farkas_coeffs(assertions, assertion_coeffs);
            if (!result) {
                STRACE("predabst", tout << "Cannot solve clauses: not a system of linear (in)equalities\n";);
                return core_clause_solutions();
            }

            STRACE("predabst", tout << "Farkas coefficients are: " << assertion_coeffs << "\n";);

            core_clause_solutions solutions;
            expr_ref_vector name2solution(m);
            for (unsigned i = clauses.size() - 1; i > 0; --i) { // skip clause 0
                core_clause const& clause = clauses[i];
                vector<int64> coeffs;
                expr_ref_vector inequalities(m);
                for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
                    coeffs.push_back(assertion_coeffs[assertion_start_index[i] + j]);
                    inequalities.push_back(to_nnf(expr_ref(clause.m_interp_body[j], m)));
                }
                for (unsigned j = 0; j < clause.m_uninterp_body.size(); ++j) {
                    coeffs.push_back(1);
                    // >>> TODO assert that head and body arguments are distinct uninterpreted constants
                    // >>> TODO assert that the head arguments and the body arguments are the same (otherwise need to do substitution); otherwise need to do substitution
                    inequalities.push_back(name2solution.get(clause.m_uninterp_body[j].m_name));
                }
                expr_ref body = make_linear_combination(coeffs, inequalities);
                // >>> TODO: assert that body has no uninterpreted constants not in head
                core_clause_solution solution(clause.m_head, body);
                STRACE("predabst", tout << "Solution for clause " << i << ": " << solution << "\n";);
                solutions.push_back(solution);
                name2solution.reserve(clause.m_head.m_name + 1);
                name2solution[clause.m_head.m_name] = body;
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

                STRACE("predabst", tout << "To reach node " << node << " (" << node->m_fdecl_info << "(" << args << ")) via rule " << ri << " requires:\n";);
                expr_ref_vector const& hvalues = node->m_explicit_values;
                vector<expr_ref_vector> bvalues;
                for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                    node_info const* qnode = node->m_parent_nodes[i];
                    bvalues.push_back(qnode->m_explicit_values);
                }
                expr_ref_vector rule_subst(m);
                expr_ref_vector terms = get_rule_terms(ri, args, hvalues, bvalues, rule_subst, substitute_template_params);
                STRACE("predabst", tout << "  " << mk_pp(mk_conj(terms), m) << "\n";);
                cs.append(terms);

                for (unsigned i = 0; i < ri->get_tail_size(); ++i) {
                    node_info const* qnode = node->m_parent_nodes[i];
                    expr_ref_vector qargs = apply_subst(ri->get_non_explicit_args(i, this), rule_subst);
                    STRACE("predabst", tout << "  reaching node " << qnode << " (" << qnode->m_fdecl_info << "(" << qargs << "))\n";);
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
            if (m_template_extras) {
                solver.assert_expr(m_template_extras);
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
                STRACE("predabst", tout << "Instantiated template parameter " << mk_pp(param, m) << " := " << mk_pp(param_value, m) << "\n";);
                m_template_param_values.push_back(param_value);
            }

            m_stats.m_num_template_instantiations++;
            return true;
        }

        void register_decl(model_ref const& md, func_decl_info const* fdecl, expr* e) const {
            STRACE("predabst", tout << "Model for " << fdecl << " is " << mk_pp(e, m) << "\n";);
            if (fdecl->m_fdecl->get_arity() == 0) {
                md->register_decl(fdecl->m_fdecl, e);
            }
            else {
                func_interp* fi = alloc(func_interp, m, fdecl->m_fdecl->get_arity());
                fi->set_else(e);
                md->register_decl(fdecl->m_fdecl, fi);
            }
        }

        void print_initial_state(std::ostream& out) const {
            out << "=====================================\n";
            out << "Initial state:\n";
            out << "  Symbols:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                     it != m_func_decl2info.end(); ++it) {
                out << "    " << it->m_value;
                if (it->m_value->m_has_template) {
                    template_info const* temp = it->m_value->m_template;
                    out << " has template " << it->m_value->m_fdecl->get_name() << "(" << temp->m_vars << ") := " << temp->m_body << std::endl;
                    CASSERT("predabst", it->m_value->m_users.empty());
                }
                else {
                    out << " is used by rules " << it->m_value->m_users << std::endl;
                }
            }
            out << "  Rules:" << std::endl;
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                out << "    " << i << ": ";
                m_rules[i]->m_rule->display_smt2(m, out);
                out << std::endl;
            }
            out << "=====================================\n";
        }

        void print_refinement_state(std::ostream& out, unsigned refine_count) const {
            out << "=====================================\n";
            out << "State before refinement step " << refine_count << ":\n";
            out << "  Symbols:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                it != m_func_decl2info.end(); ++it) {
                if (it->m_value->m_has_template) {
                    CASSERT("predabst", it->m_value->m_preds.empty());
                }
                else {
                    out << "    " << it->m_value << " has ";
                    if (it->m_value->m_preds.empty()) {
                        out << "no ";
                    }
                    out << "predicates " << it->m_value->m_preds;
                    if (it->m_value->m_new_preds > 0) {
                        out << " (last " << it->m_value->m_new_preds << " new)";
                    }
                    out << std::endl;
                }
            }
            out << "  Template parameter instances:" << std::endl;
            CASSERT("predabst", m_template_params.size() == m_template_param_values.size());
            for (unsigned i = 0; i < m_template_params.size(); ++i) {
                expr* param = m_template_params.get(i);
                expr* param_value = m_template_param_values.get(i);
                out << "    " << i << ": " << mk_pp(param, m) << " := " << mk_pp(param_value, m) << std::endl;
            }
            out << "  Instantiated rules:" << std::endl;
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                out << "    " << i << ":" << std::endl;
                m_rules[i]->m_instance_info.display(out, m_rules[i], this);
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
                    << "] and values (" << node->m_explicit_values
                    << ") for " << node->m_fdecl_info
                    << std::endl;
            }
            out << "  Max reached nodes:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                it != m_func_decl2info.end(); ++it) {
                if (it->m_value->m_has_template) {
                    CASSERT("predabst", it->m_value->m_max_reach_nodes.empty());
                }
                else {
                    out << "    " << it->m_value << ": "
                        << it->m_value->m_max_reach_nodes << std::endl;
                }
            }
            out << "  Worklist: " << m_node_worklist << std::endl;
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
