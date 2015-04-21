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
#include "dl_transforms.h"
#include "fixedpoint_params.hpp"
#include "iz3mgr.h"
#include "iz3interp.h"
#include <vector>
#include <map>
#include <algorithm>

#define PREDABST_COMPLETE_CUBE
#define PREDABST_ORDER_CARTPROD_CHOICES
#undef PREDABST_ASSERT_EXPR_UPFRONT
#define PREDABST_PRE_SIMPLIFY
#define PREDABST_NO_SIMPLIFY

namespace datalog {

    struct core_tree_node {
        unsigned         m_node_id;
        bool             m_visited;
        vector<unsigned> m_names;
        core_tree_node(unsigned node_id) :
            m_visited(false),
            m_node_id(node_id) {}
    };

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

    typedef vector<core_tree_node> core_tree;
    typedef vector<core_clause> core_clauses; // just a sequence; the index has no meaning
    typedef vector<core_clause_solution> core_clause_solutions; // ditto

    class predabst::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            /*
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsumed;
            */
            unsigned m_num_refinement_iterations;
            unsigned m_num_predabst_iterations;
            unsigned m_num_solver_assert_invocations;
            unsigned m_num_solver_check_interp_invocations;
            unsigned m_num_solver_check_body_invocations;
            unsigned m_num_solver_check_head_invocations;
            unsigned m_num_rules_unsatisfiable;
            unsigned m_num_rules_succeeded;
            unsigned m_num_rules_failed;
            unsigned m_num_nodes_created;
            unsigned m_num_nodes_suppressed;
            unsigned m_num_nodes_subsumed;
        };

        class scoped_push {
            smt::kernel& s;
        public:
            scoped_push(smt::kernel& s) : s(s) { s.push(); }
            ~scoped_push() { s.pop(1); }
        };

        typedef vector<bool> cube_t;
        typedef vector<unsigned> node_vector;
        typedef uint_set node_set;
        //typedef uint_set rule_set; // rule_set has another meaning; use node_id_set/rule_id_set?

        struct pred_info {
            expr_ref         m_pred;
            bool             m_root_pred;
#ifndef PREDABST_COMPLETE_CUBE
            vector<unsigned> m_implied;
#endif
            pred_info(expr_ref const& pred) :
                m_pred(pred),
                m_root_pred(false) {}
            pred_info(app_ref const& pred) :
                m_pred(expr_ref(pred.get(), pred.m())),
                m_root_pred(false) {}
        };

        struct func_decl_info {
            func_decl*        m_fdecl;
            expr_ref_vector   m_vars;
            vector<pred_info> m_preds;
#ifndef PREDABST_COMPLETE_CUBE
            vector<unsigned>  m_root_preds;
#endif
            uint_set          m_users;
            node_set          m_max_reach_nodes;
            bool              m_is_output_predicate;
            bool              m_is_wf_predicate;
            bool              m_has_template;
            unsigned          m_template_id;
            func_decl_info(func_decl* fdecl, expr_ref_vector const& vars, bool is_output_predicate, bool is_wf_predicate) :
                m_fdecl(fdecl),
                m_vars(vars),
                m_is_output_predicate(is_output_predicate),
                m_is_wf_predicate(is_wf_predicate),
                m_has_template(false),
                m_template_id(0) {}
            friend std::ostream& operator<<(std::ostream& out, func_decl_info const& fi) {
                out << fi.m_fdecl->get_name();
                return out;
            }
        };

        struct rule_info;

#ifdef PREDABST_ASSERT_EXPR_UPFRONT
        struct rule_instance_info {
            expr_ref_vector         m_head_pred_cond_vars;
            vector<expr_ref_vector> m_body_pred_cond_vars;
            smt::kernel*            m_rule_solver;
            rule_instance_info(ast_manager& m) :
                m_head_pred_cond_vars(m),
                m_rule_solver(NULL) {}
            void reset() {
                m_head_pred_cond_vars.reset();
                m_body_pred_cond_vars.reset();
                m_rule_solver->reset();
            }
            void cancel() {
                m_rule_solver->cancel();
            }
            void reset_cancel() {
                m_rule_solver->reset_cancel();
            }
            void alloc_solver(ast_manager& m, smt_params& fparams) {
                CASSERT("predabst", !m_rule_solver);
                m_rule_solver = alloc(smt::kernel, m, fparams);
            }
            void dealloc_solver() {
                CASSERT("predabst", m_rule_solver);
                dealloc(m_rule_solver);
                m_rule_solver = NULL;
            }
            void display(std::ostream& out, rule_info const& info) const {
                out << "      head preds cond vars (" << info.get_decl()->get_name() << "): " << m_head_pred_cond_vars << "\n";
                CASSERT("predabst", info.get_tail_size() == m_body_pred_cond_vars.size());
                for (unsigned i = 0; i < info.get_tail_size(); ++i) {
                    out << "      body pred cond vars " << i << " (" << info.get_decl(i)->get_name() << "): " << m_body_pred_cond_vars[i] << "\n";
                }
            }
        };
#else
        struct rule_instance_info {
            expr_ref_vector         m_body;
            expr_ref_vector         m_head_preds;
            vector<expr_ref_vector> m_body_preds;
            rule_instance_info(ast_manager& m) :
                m_body(m),
                m_head_preds(m) {}
            void reset() {
                m_body.reset();
                m_head_preds.reset();
                m_body_preds.reset();
            }
            void cancel() {}
            void reset_cancel() {}
            void alloc_solver(ast_manager& m, smt_params& fparams) {}
            void dealloc_solver() {}
            void display(std::ostream& out, rule_info const& info, imp const* _this) const {
                out << "      head preds (" << info.get_decl(_this) << "): " << m_head_preds << "\n";
                CASSERT("predabst", info.get_tail_size() == m_body_preds.size());
                for (unsigned i = 0; i < info.get_tail_size(); ++i) {
                    out << "      body preds " << i << " (" << info.get_decl(i, _this) << "): " << m_body_preds[i] << "\n";
                }
                out << "      body: " << m_body << "\n";
            }
        };
#endif

        struct rule_info {
            unsigned                m_id;
            rule*                   m_rule;
            vector<unsigned>        m_uninterp_pos;
            rule_instance_info      m_instance_info;
            bool                    m_unsat;
            ast_manager&            m;
            rule_info(unsigned id, rule* rule, ast_manager& m) :
                m_id(id),
                m_rule(rule),
                m_instance_info(m),
                m(m) {}
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
            func_decl_info& get_decl(imp const* _this) const {
                return *_this->m_func_decl2info[get_head()->get_decl()];
            }
            func_decl_info& get_decl(unsigned i, imp const* _this) const {
                return *_this->m_func_decl2info[get_tail(i)->get_decl()];
            }
            expr_ref_vector get_args() const {
                return expr_ref_vector(m, get_head()->get_num_args(), get_head()->get_args());
            }
            expr_ref_vector get_args(unsigned i) const {
                return expr_ref_vector(m, get_tail(i)->get_num_args(), get_tail(i)->get_args());
            }
            friend std::ostream& operator<<(std::ostream& out, rule_info const& ri) {
                out << ri.m_id;
                return out;
            }
        };

        struct node_info {
            unsigned        m_id;
            func_decl_info& m_fdecl_info;
            cube_t          m_cube;
            unsigned        m_parent_rule;
            node_vector     m_parent_nodes;
            node_info(unsigned id, func_decl_info& fdecl_info, cube_t const& cube, unsigned parent_rule, node_vector const& parent_nodes) :
                m_id(id),
                m_fdecl_info(fdecl_info),
                m_cube(cube),
                m_parent_rule(parent_rule),
                m_parent_nodes(parent_nodes) {}
            friend std::ostream& operator<<(std::ostream& out, node_info const& node) {
                out << node.m_id;
                return out;
            }
        };

        struct template_info {
            expr_ref_vector m_vars;
            expr_ref_vector m_body;
            template_info(expr_ref_vector const& vars, expr_ref_vector const& body) :
                m_vars(vars),
                m_body(body) {}
        };

        static const unsigned NON_NODE = UINT_MAX;

        ast_manager&           m;             // manager for ASTs. It is used for managing expressions
        fixedpoint_params const& m_fp_params;
        smt_params             m_fparams;     // parameters specific to smt solving
#ifndef PREDABST_ASSERT_EXPR_UPFRONT
        smt::kernel            m_solver;      // basic SMT solver class
#endif
        mutable var_subst      m_var_subst;   // substitution object. It gets updated and reset.
#ifdef PREDABST_PRE_SIMPLIFY
        simplifier             m_simplifier;
#endif
        volatile bool          m_cancel;      // Boolean flag to track external cancelation.
        stats                  m_stats;       // statistics information specific to the predabst module.

        func_decl_ref_vector                m_func_decls;
        obj_map<func_decl, func_decl_info*> m_func_decl2info;
        vector<rule_info>                   m_rules;
        vector<node_info>                   m_nodes;
        node_set                            m_node_worklist;

        expr_ref_vector                     m_template_params;
        expr_ref_vector                     m_template_param_values;
        expr_ref                            m_template_extras;
        vector<template_info>               m_templates;
        expr_ref_vector                     m_template_constraint_vars;
        expr_ref_vector                     m_template_constraints;

        typedef enum { reached_query, bad_template, not_wf } acr_error_kind;

        struct acr_error {
            unsigned       m_node_id;
            acr_error_kind m_kind;
            acr_error() {}
            acr_error(unsigned node_id, acr_error_kind kind) :
                m_node_id(node_id),
                m_kind(kind) {}
        };

        struct core_tree_info {
            unsigned                m_last_name;
            unsigned                m_last_pos;
            core_tree               m_core;
            vector<func_decl_info*> m_name2func_decl;
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
#ifndef PREDABST_ASSERT_EXPR_UPFRONT
            m_solver(m, m_fparams),
#endif
            m_var_subst(m, false),
#ifdef PREDABST_PRE_SIMPLIFY
            m_simplifier(m),
#endif
            m_cancel(false),
            m_func_decls(m),
            m_template_params(m),
            m_template_param_values(m),
            m_template_extras(m),
            m_template_constraints(m),
            m_template_constraint_vars(m) {

            m_fparams.m_mbqi = false;
            m_fparams.m_model = false;
#ifdef PREDABST_NO_SIMPLIFY
            m_fparams.m_preprocess = false;
#endif

#ifdef PREDABST_PRE_SIMPLIFY
            basic_simplifier_plugin* bsimp = alloc(basic_simplifier_plugin, m);
            m_simplifier.register_plugin(bsimp);
            m_simplifier.register_plugin(alloc(arith_simplifier_plugin, m, *bsimp, m_fparams));
#endif

            reg_decl_plugins(m);
        }

        ~imp() {
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                it != m_func_decl2info.end(); ++it) {
                dealloc(it->m_value);
            }
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                m_rules[i].m_instance_info.dealloc_solver();
            }
        }

        lbool query(rule_set& rules) {
            find_all_func_decls(rules);

            // Some of the rules are actually declarations of templates, extra
            // constraints on templates, and predicate lists.  Find these, and
            // remove them from the rule set.  Note that we must process the
            // extra template constraints before the templates, in order that we
            // know how many extra arguments each template has, and we must
            // process the templates before the predicate lists, in order to
            // reject predicate lists for templated predicate symbols.
            process_special_rules(rules, is_template_extra, &imp::collect_template_extra);
            process_special_rules(rules, is_template, &imp::collect_template);
            process_special_rules(rules, is_predicate_list, &imp::collect_predicate_list);

            CASSERT("predabst", m_rules.empty());
            for (unsigned i = 0; i < rules.get_num_rules(); ++i) {
                rule* r = rules.get_rule(i);
                m_rules.push_back(rule_info(m_rules.size(), r, m));
                rule_info& ri = m_rules.back();
                ri.m_instance_info.alloc_solver(m, m_fparams);

                CASSERT("predabst", is_regular_predicate(r->get_decl()));
                for (unsigned j = 0; j < r->get_uninterpreted_tail_size(); ++j) {
                    CASSERT("predabst", is_regular_predicate(r->get_decl(j)));
                    if (!m_func_decl2info[r->get_decl(j)]->m_has_template) {
                        ri.m_uninterp_pos.push_back(j);
                        m_func_decl2info[r->get_decl(j)]->m_users.insert(i);
                    }
                }
            }

            return abstract_check_refine();
        }

        void cancel() {
            m_cancel = true;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                m_rules[i].m_instance_info.cancel();
            }
#else
            m_solver.cancel();
#endif
        }

        void cleanup() {
            m_cancel = false;
            // TBD hmm?
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                m_rules[i].m_instance_info.reset_cancel();
            }
#else
            m_solver.reset_cancel();
#endif
        }

        void reset_statistics() {
            m_stats.reset();
        }

        void collect_statistics(statistics& st) const {
#define UPDATE_STAT(NAME) st.update(#NAME, m_stats.NAME)
            UPDATE_STAT(m_num_refinement_iterations);
            UPDATE_STAT(m_num_predabst_iterations);
            UPDATE_STAT(m_num_solver_assert_invocations);
            UPDATE_STAT(m_num_solver_check_interp_invocations);
            UPDATE_STAT(m_num_solver_check_head_invocations);
            UPDATE_STAT(m_num_solver_check_body_invocations);
            UPDATE_STAT(m_num_rules_unsatisfiable);
            UPDATE_STAT(m_num_rules_succeeded);
            UPDATE_STAT(m_num_rules_failed);
            UPDATE_STAT(m_num_nodes_created);
            UPDATE_STAT(m_num_nodes_suppressed);
            UPDATE_STAT(m_num_nodes_subsumed);
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
                func_decl_info const& fi = *m_func_decl2info[m_func_decls[i]];
                // Note that the generated model must be in terms of
                // get_arg_vars(fi.m_fdecl); we generate the model in terms of
                // fi.m_vars, which we assume to be the same.
                if (fi.m_is_output_predicate) {
                    // query symbols are ignored
                }
                else if (fi.m_has_template) {
                    // templated predicate symbols are instantiated
                    template_info const& temp = m_templates[fi.m_template_id];
                    expr_ref_vector temp_subst = get_temp_subst_vect(temp, fi.m_vars);
                    expr_ref body = mk_conj(apply_subst(temp.m_body, temp_subst));
                    register_decl(md, fi.m_fdecl, body);
                }
                else {
                    // other predicate symbols are concretized
                    node_set const& nodes = fi.m_max_reach_nodes;
                    expr_ref_vector disj(m);
                    for (node_set::iterator it = nodes.begin(); it != nodes.end(); ++it) {
                        cube_t const& cube = m_nodes[*it].m_cube;
                        disj.push_back(cube_to_formula(cube, fi.m_preds));
                    }
                    register_decl(md, fi.m_fdecl, mk_disj(disj));
                }
            }
            return md;
        }

    private:

        // Returns true if v1 is a (possibly non-strict) subset of v2.
        static bool is_subset(expr_ref_vector const& v1, expr_ref_vector const& v2) {
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

        // Apply a substitution vector to each expression in a vector of
        // expressions, returning the result.
        expr_ref_vector apply_subst(vector<pred_info> const& preds, expr_ref_vector const& subst) const {
            expr_ref_vector exprs2(m);
            exprs2.reserve(preds.size());
            for (unsigned i = 0; i < preds.size(); ++i) {
                exprs2[i] = apply_subst(preds[i].m_pred, subst);
            }
            return exprs2;
        }

        // Returns a substitution vector that maps each variable in vars to the
        // corresponding expression in exprs.
        expr_ref_vector build_subst(unsigned n, expr* const* vars, expr* const* exprs) const {
            expr_ref_vector inst(m);
            inst.reserve(n); // note that this is not necessarily the final size of inst
            for (unsigned i = 0; i < n; ++i) {
                CASSERT("predabst", is_var(vars[i]));
                unsigned idx = to_var(vars[i])->get_idx();
                inst.reserve(idx + 1);
                CASSERT("predabst", !inst.get(idx));
                inst[idx] = exprs[i];
            }
            return inst;
        }

        expr_ref_vector build_subst(expr* const* vars, expr_ref_vector const& exprs) const {
            return build_subst(exprs.size(), vars, exprs.c_ptr());
        }

        expr_ref_vector build_subst(expr_ref_vector const& vars, expr* const* exprs) const {
            return build_subst(vars.size(), vars.c_ptr(), exprs);
        }

        expr_ref_vector build_subst(expr_ref_vector const& vars, expr_ref_vector const& exprs) const {
            CASSERT("predabst", vars.size() == exprs.size());
            return build_subst(vars.size(), vars.c_ptr(), exprs.c_ptr());
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
        expr_ref_vector get_arg_vars(func_decl* fdecl) const {
            expr_ref_vector args(m);
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
        expr_ref_vector get_subst_vect(rule const* r, expr_ref_vector const& hvars, char const* prefix, expr_ref_vector& unification_terms) const {
            CASSERT("predabst", hvars.size() == r->get_decl()->get_arity());

            used_vars used;
            // The following is a clone of r->get_used_vars(&used), which is unfortunately inaccessible.
            used.process(r->get_head());
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                used.process(r->get_tail(i));
            }

            expr_ref_vector rule_subst(m);
            rule_subst.reserve(used.get_max_found_var_idx_plus_1());

            // Variables that appear bare in the head are mapped to the value of the first corresponding argument.
            vector<bool> constraint_needed;
            for (unsigned i = 0; i < r->get_decl()->get_arity(); ++i) {
                bool assigned = false;
                if (is_var(r->get_head()->get_arg(i))) {
                    unsigned idx = to_var(r->get_head()->get_arg(i))->get_idx();
                    CASSERT("predabst", idx < rule_subst.size());
                    if (!rule_subst.get(idx)) {
                        rule_subst[idx] = hvars.get(i);
                        assigned = true;
                    }
                }
                constraint_needed.push_back(!assigned);
            }

            // Other variables are mapped to fresh constants.
            for (unsigned i = 0; i < used.get_max_found_var_idx_plus_1(); ++i) {
                if (!rule_subst.get(i)) {
                    sort* s = used.get(i);
                    if (s) {
                        app *c = m.mk_fresh_const(prefix, s);
                        rule_subst[i] = c;
                    }
                }
            }

            // Generate constraints for all head argument positions that were not mapped directly to the corresponding argument.
            CASSERT("predabst", unification_terms.empty());
            for (unsigned i = 0; i < r->get_decl()->get_arity(); ++i) {
                if (constraint_needed[i]) {
                    unification_terms.push_back(m.mk_eq(apply_subst(r->get_head()->get_arg(i), rule_subst), hvars.get(i)));
                }
            }

            return rule_subst;
        }

        // Returns a substitution vector mapping each variable used in r to a
        // fresh constant.
        expr_ref_vector get_subst_vect_free(rule const* r, char const* prefix) const {
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
                    app *c = m.mk_fresh_const(prefix, s);
                    rule_subst[i] = c;
                }
            }

            return rule_subst;
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) for template temp, which maps the head arguments to hvars
        // and the extra template parameters to their instantiated values.
        expr_ref_vector get_temp_subst_vect(template_info const& temp, expr_ref_vector const& hvars) const {
            return build_subst(temp.m_vars, vector_concat(hvars, m_template_param_values));
        }

        // Returns a substitution vector (i.e. a vector indexed by variable
        // number) for template temp, which maps the head arguments to hvars
        // and the extra template parameters to their corresponding
        // uninterpreted constants.
        expr_ref_vector get_temp_subst_vect_noparams(template_info const& temp, expr_ref_vector const& hvars) const {
            return build_subst(temp.m_vars, vector_concat(hvars, m_template_params));
        }

        expr_ref_vector get_rule_body(rule* r, expr_ref_vector const& rule_subst, bool substitute_template_params = true) const {
            unsigned usz = r->get_uninterpreted_tail_size();
            unsigned tsz = r->get_tail_size();
            expr_ref_vector body = apply_subst(expr_ref_vector(m, tsz - usz, r->get_expr_tail() + usz), rule_subst);
            for (unsigned i = 0; i < usz; ++i) {
                func_decl_info const& fi = *m_func_decl2info[r->get_decl(i)];
                if (fi.m_has_template) {
                    template_info const& temp = m_templates[fi.m_template_id];
                    expr_ref_vector temp_args = apply_subst(expr_ref_vector(m, r->get_tail(i)->get_num_args(), r->get_tail(i)->get_args()), rule_subst);
                    expr_ref_vector temp_subst(m);
                    if (substitute_template_params) {
                        temp_subst.swap(get_temp_subst_vect(temp, temp_args));
                    } else {
                        temp_subst.swap(get_temp_subst_vect_noparams(temp, temp_args));
                    }
                    body.append(apply_subst(temp.m_body, temp_subst));
                }
            }
            return body;
        }

        expr_ref_vector get_rule_terms(rule* r, expr_ref_vector const& args, expr_ref_vector& rule_subst, bool substitute_template_params = true) const {
            CASSERT("predabst", rule_subst.empty());
            expr_ref_vector unification_terms(m);
            rule_subst.swap(get_subst_vect(r, args, "s", unification_terms));
            expr_ref_vector body_terms = get_rule_body(r, rule_subst, substitute_template_params);
            return vector_concat(unification_terms, body_terms);
        }

        static bool args_are_distinct_vars(app* a) {
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
            }
            return true;
        }

        // Returns true if e contains any variables other than those in bound.
        static bool has_free_vars(expr* e, expr_ref_vector const& bound) {
            if (is_var(e)) {
                return !bound.contains(e);
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
            return has_free_vars(e, expr_ref_vector(m));
        }

#ifndef PREDABST_COMPLETE_CUBE
        static void add_implied_to_cube(cube_t& cube, vector<pred_info> const& preds, unsigned idx) {
            CASSERT("predabst", !cube[idx]);
            cube[idx] = true;
            for (unsigned i = 0; i < preds[idx].m_implied.size(); ++i) {
                add_implied_to_cube(cube, preds, preds[idx].m_implied[i]);
            }
        }

        // Return the completion of cube, i.e. the vector containing all predicates that are implied by those in cube.
        static cube_t complete_cube(cube_t const& cube, func_decl_info const& fi) {
            cube_t completion;
            for (unsigned i = 0; i < cube.size(); ++i) {
                if (cube[i]) {
                    add_implied_to_cube(completion, fi.m_preds, i);
                }
            }
            return completion;
        }
#endif

        // Returns whether c1 implies c2, or in other words, whether the set
        // represented by c1 is a (non-strict) subset of that represented by c2.
        static bool complete_cube_leq(cube_t const& c1, cube_t const& c2) {
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

        static bool cube_leq(cube_t const& c1, cube_t const& c2, func_decl_info const& fi) {
#ifdef PREDABST_COMPLETE_CUBE
            return complete_cube_leq(c1, c2);
#else
            return complete_cube_leq(complete_cube(c1, fi), c2);
#endif
        }

        expr_ref cube_to_formula(cube_t const& cube, vector<pred_info> const& preds) const {
            expr_ref_vector es(m);
            for (unsigned i = 0; i < cube.size(); ++i) {
                if (cube[i]) {
                    es.push_back(preds[i].m_pred);
                }
            }
            return mk_conj(es);
        }

        static bool is_regular_predicate(func_decl const* fdecl) {
            return !is_template_extra(fdecl) && !is_template(fdecl) && !is_predicate_list(fdecl);
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
                        if (is_predicate_list(fdecl)) {
                            STRACE("predabst", tout << "Error: found predicate list " << fdecl->get_name() << " in non-head position\n";);
                            throw default_exception("found predicate list " + fdecl->get_name().str() + " in non-head position");
                        }
                        process_func_decl(rules, fdecl);
                    }
                    process_func_decl(rules, r->get_decl());
                }
            }
        }

        void process_func_decl(rule_set const& rules, func_decl *fdecl) {
            CASSERT("predabst", is_regular_predicate(fdecl));
            CASSERT("predabst", fdecl->get_range() == m.mk_bool_sort());
            if (!m_func_decl2info.contains(fdecl)) {
                bool is_wf = is_wf_predicate(fdecl);
                if (is_wf) {
                    if (fdecl->get_arity() % 2 != 0) {
                        STRACE("predabst", tout << "Error: WF predicate symbol " << fdecl->get_name() << " has arity " << fdecl->get_arity() << " which is odd\n";);
                        throw default_exception("WF predicate symbol " + fdecl->get_name().str() + " has odd arity");
                    }
                    for (unsigned i = 0; i < fdecl->get_arity() / 2; ++i) {
                        unsigned j = fdecl->get_arity() / 2 + i;
                        if (fdecl->get_domain(i) != fdecl->get_domain(j)) {
                            STRACE("predabst", tout << "Error: WF predicate symbol " << fdecl->get_name() << " has argument " << i << " of type " << mk_pp(fdecl->get_domain(i), m) << " and argument " << j << " of type " << mk_pp(fdecl->get_domain(j), m) << "\n";);
                            throw default_exception("WF predicate symbol " + fdecl->get_name().str() + " has mismatching argument types");
                        }
                        // The following restriction may be removed in future.
                        if (fdecl->get_domain(i) != arith_util(m).mk_int()) {
                            STRACE("predabst", tout << "Error: WF predicate symbol " << fdecl->get_name() << " has argument " << i << " of type " << mk_pp(fdecl->get_domain(i), m) << " which is not int\n";);
                            throw default_exception("WF predicate symbol " + fdecl->get_name().str() + " has non-integer argument types");
                        }
                    }
                }

                m_func_decls.push_back(fdecl);
                expr_ref_vector vars = get_arg_vars(fdecl);
                m_func_decl2info.insert(fdecl, alloc(func_decl_info, fdecl, vars, rules.is_output_predicate(fdecl), is_wf));
            }
        }

        bool is_wf_predicate(func_decl const* pred) const {
            return pred->get_name().str().substr(0, 6) == "__wf__";
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

            if (!args_are_distinct_vars(r->get_head())) {
                STRACE("predabst", tout << "Error: extra template constraint has invalid argument list\n";);
                throw default_exception("extra template constraint has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: extra template constraint has an uninterpreted tail\n";);
                throw default_exception("extra template constraint has an uninterpreted tail");
            }

            // Replace the variables corresponding to the extra template parameters with fresh constants.
            expr_ref_vector extra_params = get_fresh_args(r->get_decl(), "b");
            expr_ref_vector extra_subst = build_subst(r->get_head()->get_args(), extra_params);
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

            func_decl_info& fi = *m_func_decl2info[suffix_decl];
            CASSERT("predabst", !fi.m_is_output_predicate);
            if (fi.m_is_wf_predicate) {
                STRACE("predabst", tout << "Error: found template for WF predicate symbol\n";);
                throw default_exception("found template for WF predicate symbol " + suffix.str());
            }

            if (fi.m_has_template) {
                STRACE("predabst", tout << "Error: found multiple templates for " << suffix.str() << "\n";);
                throw default_exception("found multiple templates for " + suffix.str());
            }

            fi.m_has_template = true;
            fi.m_template_id = m_templates.size();

            if (!args_are_distinct_vars(r->get_head())) {
                STRACE("predabst", tout << "Error: template has invalid argument list\n";);
                throw default_exception("template for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: template has an uninterpreted tail\n";);
                throw default_exception("template for " + suffix.str() + " has an uninterpreted tail");
            }

            expr_ref_vector vars = get_arg_vars(r->get_decl());
            expr_ref_vector subst = build_subst(r->get_head()->get_args(), vars);
            expr_ref_vector body(m);
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                if (has_free_vars(r->get_tail(i), expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()))) {
                    STRACE("predabst", tout << "Error: template has free variables\n";);
                    throw default_exception("template for " + suffix.str() + " has free variables");
                }
                body.push_back(apply_subst(r->get_tail(i), subst));
            }
            STRACE("predabst", tout << "  " << suffix_decl->get_name() << "(" << vars << ") := " << body << "\n";);
            m_templates.push_back(template_info(vars, body));
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

            func_decl_info& fi = *m_func_decl2info[suffix_decl];
            CASSERT("predabst", !fi.m_is_output_predicate);
            if (fi.m_has_template) {
                STRACE("predabst", tout << "Error: found predicate list for templated predicate symbol\n";);
                throw default_exception("found predicate list for templated predicate symbol " + suffix.str());
            }

            if (!args_are_distinct_vars(r->get_head())) {
                STRACE("predabst", tout << "Error: predicate list has invalid argument list\n";);
                throw default_exception("predicate list for " + suffix.str() + " has invalid argument list");
            }

            if (r->get_uninterpreted_tail_size() != 0) {
                STRACE("predabst", tout << "Error: predicate list has an uninterpreted tail\n";);
                throw default_exception("predicate list for " + suffix.str() + " has an uninterpreted tail");
            }

            // Add p1..pN to m_func_decl2info[SUFFIX].m_preds.
            CASSERT("predabst", !fi.m_is_output_predicate);
            expr_ref_vector subst = build_subst(r->get_head()->get_args(), fi.m_vars);
            for (unsigned i = 0; i < r->get_tail_size(); ++i) {
                if (has_free_vars(r->get_tail(i), expr_ref_vector(m, r->get_head()->get_num_args(), r->get_head()->get_args()))) {
                    STRACE("predabst", tout << "Error: predicate has free variables\n";);
                    throw default_exception("predicate for " + suffix.str() + " has free variables");
                }

                app_ref pred = apply_subst(r->get_tail(i), subst);
                STRACE("predabst", tout << "  predicate " << i << ": " << mk_pp(pred, m) << "\n";);
                fi.m_preds.push_back(pred_info(pred));
            }
        }

#define RETURN_CHECK_CANCELLED(result) return m_cancel ? l_undef : result;

        lbool abstract_check_refine() {
            STRACE("predabst", print_initial_state(tout););

            if (!instantiate_templates()) {
                STRACE("predabst", tout << "Initial template refinement unsuccessful: result is UNSAT\n";);
                RETURN_CHECK_CANCELLED(l_true);
            }

            // The only things that change on subsequent iterations of this loop are
            // the predicate lists
            // (m_func_decl2info::m_preds) and template instances.  The latter can have an
            // effect on the execution of the algorithm via the initial nodes
            // set up by initialize_abs.
            unsigned refine_count = 0;
            while (true) {
                m_stats.m_num_refinement_iterations++;
                m_nodes.reset();
                for (unsigned i = 0; i < m_func_decls.size(); ++i) {
                    func_decl_info& fi = *m_func_decl2info[m_func_decls.get(i)];
                    fi.m_max_reach_nodes.reset();
                    if (fi.m_has_template) {
                        // Create a dummy node representing the template instance.
                        m_stats.m_num_nodes_created++;
                        cube_t cube(m_templates[fi.m_template_id].m_body.size(), true);
                        m_nodes.push_back(node_info(m_nodes.size(), fi, cube, (unsigned)-1, node_vector()));
                        node_info const& node = m_nodes.back();
                        fi.m_max_reach_nodes.insert(node.m_id);
                    }
                    else {
#ifndef PREDABST_COMPLETE_CUBE
                        // Set up m_func_decl2info::m_preds::m_implied for this iteration.
                        for (unsigned j = 0; j < fi.m_preds.size(); ++j) {
                            fi.m_preds[j].m_implied.reset();
                            fi.m_preds[j].m_root_pred = true;
                        }

                        expr_ref_vector subst = build_subst(fi.m_vars, get_fresh_args(fi.m_fdecl, "a"));
                        expr_ref_vector inst_preds = apply_subst(fi.m_preds, subst);

                        for (unsigned j = 0; j < fi.m_preds.size(); ++j) {
                            for (unsigned k = 0; k < fi.m_preds.size(); ++k) {
                                if (j != k) {
                                    // Does preds[j] imply preds[k]?
                                    smt_params new_param;
                                    smt::kernel solver(m, new_param);
                                    solver.assert_expr(inst_preds.get(j));
                                    solver.assert_expr(expr_ref(m.mk_not(inst_preds.get(k)), m));
                                    if (solver.check() != l_false) {
                                        // preds[j] implies preds[k].
                                        fi.m_preds[j].m_implied.push_back(k);
                                        fi.m_preds[k].m_root_pred = false;
                                    }
                                }
                            }
                        }

                        fi.m_root_preds.reset();
                        for (unsigned j = 0; j < fi.m_preds.size(); ++j) {
                            if (fi.m_preds[j].m_root_pred) {
                                fi.m_root_preds.push_back(j);
                            }
                        }

                        STRACE("predabst", print_preds_forest(tout, fi););

                        // Debug code: check that every predicate appears precisely once in the forest.
                        cube_t full_cube;
                        full_cube.resize(fi.m_preds.size());
                        for (unsigned j = 0; j < fi.m_root_preds.size(); ++j) {
                            add_implied_to_cube(full_cube, fi.m_preds, fi.m_root_preds[j]);
                        }
                        for (unsigned j = 0; j < full_cube.size(); ++j) {
                            CASSERT("predabst", full_cube[j]);
                        }
#endif
                    }
                }

                // Set up m_rules for this iteration:
                // for each rule: ground body and instantiate predicates for applications
                for (unsigned i = 0; !m_cancel && i < m_rules.size(); ++i) {
                    rule_info& ri = m_rules[i];
                    instantiate_rule(ri);
                    ri.m_unsat = !rule_body_satisfiable(ri);
                }

                STRACE("predabst", print_refinement_state(tout, refine_count););

                acr_error error;
                if (find_solution(refine_count, error)) {
                    STRACE("predabst", tout << "Solution found: result is SAT\n";);
                    RETURN_CHECK_CANCELLED(l_false);
                }
                else if (!m_fp_params.use_refinement()) {
                    STRACE("predabst", tout << "No solution found: result is UNSAT\n";);
                    RETURN_CHECK_CANCELLED(l_true);
                }
                else {
                    // Our attempt to find a solution failed and we want to try refinement.
                    core_tree_info core_info;
                    core_tree_wf_info core_info_wf(m);
                    core_tree_template_info core_info_template(m);
                    node_info const& error_node = m_nodes[error.m_node_id];
                    expr_ref_vector error_args = get_fresh_args(error_node.m_fdecl_info.m_fdecl, "r");
                    if (not_reachable_without_abstraction(error_node, error_args, core_info)) {
                        // The problem node isn't reachable without abstraction.
                        // We need to refine the abstraction and retry.
                        if (!refine_predicates_not_reachable(error_args, core_info)) {
                            STRACE("predabst", tout << "Predicate refinement unsuccessful: result is UNKNOWN\n";);
                            RETURN_CHECK_CANCELLED(l_undef);
                        }

                        STRACE("predabst", tout << "Predicate refinement successful: retrying\n";);
                    }
                    else if ((error.m_kind == bad_template) && good_template_without_abstraction(error_node, error_args, core_info_template)) {
                        // The problem node implies the template instance without abstraction.
                        // We need to refine the abstraction and retry.
                        if (!refine_predicates_good_template(error_args, core_info, core_info_template)) {
                            STRACE("predabst", tout << "Template predicate refinement unsuccessful: result is UNKNOWN\n";);
                            RETURN_CHECK_CANCELLED(l_undef);
                        }

                        STRACE("predabst", tout << "Template predicate refinement successful: retrying\n";);
                    }
                    else if ((error.m_kind == not_wf) && wf_without_abstraction(error_node, error_args, core_info_wf)) {
                        // The problem node is well-founded without abstraction.
                        // We need to refine the abstraction and retry.
                        if (!refine_predicates_wf(error_args, core_info, core_info_wf)) {
                            STRACE("predabst", tout << "WF predicate refinement unsuccessful: result is UNKNOWN\n";);
                            RETURN_CHECK_CANCELLED(l_undef);
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
                            RETURN_CHECK_CANCELLED(l_true);
                        }

                        STRACE("predabst", tout << "Template refinement successful: retrying\n";);
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

        void pre_simplify(expr_ref_vector& exprs) {
#ifdef PREDABST_PRE_SIMPLIFY
            for (unsigned i = 0; i < exprs.size(); ++i) {
                proof_ref pr(m);
                expr_ref e(exprs.get(i), m);
                m_simplifier(e, e, pr);
                exprs[i] = e;
            }
#endif
        }

        void instantiate_rule(rule_info& ri) {
            STRACE("predabst", tout << "Instantiating rule " << ri << "\n";);
            rule_instance_info& info = ri.m_instance_info;
            info.reset();

            // create grounding substitution
            expr_ref_vector rule_subst = get_subst_vect_free(ri.m_rule, "c");

            // create ground body
            expr_ref_vector body = get_rule_body(ri.m_rule, rule_subst);
            pre_simplify(body);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            for (unsigned i = 0; i < body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                info.m_rule_solver->assert_expr(body.get(i));
            }
#else
            info.m_body.swap(body);
#endif

            // create instantiations for head
            func_decl_info const& fi = ri.get_decl(this);
            expr_ref_vector heads(m);
            if (fi.m_has_template) {
                template_info const& temp = m_templates[fi.m_template_id];
                expr_ref_vector temp_subst = get_temp_subst_vect(temp, apply_subst(ri.get_args(), rule_subst));
                heads.swap(apply_subst(temp.m_body, temp_subst));
            }
            else {
                heads.swap(app_inst_preds(fi, apply_subst(ri.get_args(), rule_subst)));
            }
            invert(heads);
            pre_simplify(heads);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            expr_ref_vector head_cond_vars = assert_exprs_upfront(heads, info.m_rule_solver);
            info.m_head_pred_cond_vars.swap(head_cond_vars);
#else
            info.m_head_preds.swap(heads);
#endif

            // create instantiations for non-templated body applications
            for (unsigned i = 0; i < ri.get_tail_size(); ++i) {
                func_decl_info const& fi = ri.get_decl(i, this);
                CASSERT("predabst", !fi.m_has_template);
                expr_ref_vector tails = app_inst_preds(fi, apply_subst(ri.get_args(i), rule_subst));
                pre_simplify(tails);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                expr_ref_vector tail_cond_vars = assert_exprs_upfront(tails, info.m_rule_solver);
                info.m_body_pred_cond_vars.push_back(tail_cond_vars);
#else
                info.m_body_preds.push_back(tails);
#endif
            }
        }

        // instantiate each predicate by replacing its free variables with (grounded) arguments of gappl
        expr_ref_vector app_inst_preds(func_decl_info const& fi, expr_ref_vector const& args) {
            // instantiation maps preds variables to head arguments
            expr_ref_vector inst = build_subst(fi.m_vars, args);
            // preds instantiates to inst_preds
            return apply_subst(fi.m_preds, inst);
        }

#ifdef PREDABST_ASSERT_EXPR_UPFRONT
        expr_ref_vector assert_exprs_upfront(expr_ref_vector const& preds, smt::kernel* solver) {
            expr_ref_vector cond_vars(m);
            for (unsigned i = 0; i < preds.size(); ++i) {
                expr_ref c(m.mk_fresh_const("cv", m.mk_bool_sort()), m);
                cond_vars.push_back(c);
                expr_ref e(m.mk_iff(preds.get(i), c), m);
                m_stats.m_num_solver_assert_invocations++;
                solver->assert_expr(e);
            }
            return cond_vars;
        }
#endif

        bool rule_body_satisfiable(rule_info const& ri) {
            rule_instance_info const& info = ri.m_instance_info;

#ifndef PREDABST_ASSERT_EXPR_UPFRONT
            scoped_push _push1(m_solver);
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                m_solver.assert_expr(info.m_body[i]);
            }
#endif

            m_stats.m_num_solver_check_interp_invocations++;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            lbool result = info.m_rule_solver->check();
#else
            lbool result = m_solver.check();
#endif
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
            model_ref md = get_model();
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                rule* r = m_rules[i].m_rule;
                unsigned usz = r->get_uninterpreted_tail_size();
                unsigned tsz = r->get_tail_size();
                expr_ref_vector body_exp_terms(m, tsz - usz, r->get_expr_tail() + usz);
                for (unsigned j = 0; j < usz; ++j) {
                    body_exp_terms.push_back(model_eval_app(md, r->get_tail(j)));
                }
                expr_ref body_exp = mk_conj(body_exp_terms);
                expr_ref head_exp(m);
                if (!m_func_decl2info[r->get_decl()]->m_is_output_predicate) {
                    head_exp = model_eval_app(md, r->get_head());
                }
                else {
                    head_exp = m.mk_false();
                }

                scoped_push push(solver);
                solver.assert_expr(ground(expr_ref(m.mk_and(body_exp, mk_not(head_exp)), m), "c"));
                if (solver.check() != l_false) {
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
                for (unsigned i = 0; !m_cancel && i < m_rules.size(); ++i) {
                    rule_info const& ri = m_rules[i];
                    if (ri.get_tail_size() == 0) {
                        initialize_abs(ri);
                    }
                }

                // process worklist
                unsigned infer_count = 0;
                while (!m_cancel && !m_node_worklist.empty()) {
                    m_stats.m_num_predabst_iterations++;

                    STRACE("predabst", print_inference_state(tout, refine_count, infer_count););
                    unsigned current_id = *m_node_worklist.begin();
                    m_node_worklist.remove(current_id);
                    inference_step(current_id);
                    infer_count++;

                    if ((m_fp_params.max_predabst_iterations() > 0) &&
                        (m_stats.m_num_predabst_iterations >= m_fp_params.max_predabst_iterations())) {
                        m_cancel = true;
                    }
                }

#ifdef Z3DEBUG
                if (!m_cancel && !check_solution()) {
                    throw default_exception("check_solution failed");
                }
#endif

                // We managed to find a solution.
                return true;
            }
            catch (acr_error const& error2) {
                // We failed to find a solution.
                error = error2;
                return false;
            }
        }

        void initialize_abs(rule_info const& ri) {
            cart_pred_abst_rule(ri);
        }

        void inference_step(unsigned node_id) {
            // Find all rules whose body contains the func_decl of the new node.
            func_decl_info const& fi = m_nodes[node_id].m_fdecl_info;
            uint_set const& rules = fi.m_users;
            STRACE("predabst", tout << "Performing inference from node " << node_id << " using rules " << rules << "\n";);
            for (uint_set::iterator r_it = rules.begin(); r_it != rules.end(); ++r_it) {
                rule_info const& ri = m_rules[*r_it];
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
                    cart_pred_abst_rule(ri, *p_it, node_id);
                }
            }
        }

        uint_set get_rule_body_positions(rule_info const& ri, func_decl_info const& fi) {
            uint_set positions;
            for (unsigned i = 0; i < ri.get_tail_size(); ++i) {
                if (&ri.get_decl(i, this) == &fi) {
                    positions.insert(i);
                }
            }
            return positions;
        }

        // This is implementing the "abstract inference rules" from Figure 2 of "synthesizing software verifiers from proof rules".
        // With no 3rd argument, rule Rinit is applied; otherwise rule Rstep is applied.
        void cart_pred_abst_rule(rule_info const& ri, unsigned fixed_pos = 0, unsigned fixed_node_id = NON_NODE) {
            rule_instance_info const& info = ri.m_instance_info;
            CASSERT("predabst", (fixed_node_id == NON_NODE) || (fixed_pos < ri.get_tail_size()));

            if (ri.m_unsat) {
                STRACE("predabst", tout << "Skipping rule " << ri << " with unsatisfiable body\n";);
                return;
            }

#ifndef PREDABST_ASSERT_EXPR_UPFRONT
            scoped_push _push1(m_solver);
            for (unsigned i = 0; i < info.m_body.size(); ++i) {
                m_stats.m_num_solver_assert_invocations++;
                m_solver.assert_expr(info.m_body[i]);
            }
#endif

            vector<unsigned> positions = get_rule_position_ordering(ri, fixed_pos);
            node_vector chosen_nodes;
            expr_ref_vector cond_vars(m); // unused unless PREDABST_ASSERT_EXPR_UPFRONT defined
            cart_pred_abst_rule(ri, fixed_pos, fixed_node_id, positions, chosen_nodes, cond_vars);
        }

        vector<unsigned> get_rule_position_ordering(rule_info const& ri, unsigned fixed_pos) {
            std::vector<std::pair<unsigned, unsigned>> pos_counts;
            for (unsigned i = 0; i < ri.get_tail_size(); ++i) {
                unsigned n = (i == fixed_pos) ? 1 : ri.get_decl(i, this).m_max_reach_nodes.num_elems();
                STRACE("predabst-cprod", tout << "There are " << n << " option(s) for position " << i << "\n";);
                pos_counts.push_back(std::make_pair(n, i));
            }

#ifdef PREDABST_ORDER_CARTPROD_CHOICES
            std::stable_sort(pos_counts.begin(), pos_counts.end());
#endif

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

        bool is_implied(expr* e, rule_instance_info const& info, expr_ref_vector& cond_vars) {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            cond_vars.push_back(e);
            m_stats.m_num_solver_check_head_invocations++;
            lbool result = info.m_rule_solver->check(cond_vars.size(), cond_vars.c_ptr());
            cond_vars.pop_back();
#else
            scoped_push _push2(m_solver);
            m_stats.m_num_solver_assert_invocations++;
            m_solver.assert_expr(e);
            m_stats.m_num_solver_check_head_invocations++;
            lbool result = m_solver.check();
#endif
            return (result == l_false);
        }

#ifndef PREDABST_COMPLETE_CUBE
        void build_cube(cube_t& cube, expr_ref_vector const& es, vector<pred_info> const& preds, vector<unsigned> const& pred_idxs, rule_instance_info const& info, expr_ref_vector& cond_vars) {
            for (unsigned i = 0; i < pred_idxs.size(); ++i) {
                unsigned idx = pred_idxs[i];
                CASSERT("predabst", !cube[idx]);
                if (is_implied(es[idx], info, cond_vars)) {
                    cube[idx] = true;
                }
                else {
                    build_cube(cube, es, preds, preds[idx].m_implied, info, cond_vars);
                }
            }
        }
#endif

        static uint_set singleton_set(unsigned n) {
            uint_set s;
            s.insert(n);
            return s;
        }

        void cart_pred_abst_rule(rule_info const& ri, unsigned fixed_pos, unsigned fixed_node_id, vector<unsigned> const& positions, node_vector& chosen_nodes, expr_ref_vector& cond_vars) {
            CASSERT("predabst", positions.size() == ri.get_tail_size());
            CASSERT("predabst", chosen_nodes.size() <= ri.get_tail_size());
            rule_instance_info const& info = ri.m_instance_info;

            if (chosen_nodes.size() < ri.get_tail_size()) {
                unsigned i = positions[chosen_nodes.size()];

                node_set nodes = (i == fixed_pos) ? singleton_set(fixed_node_id) : ri.get_decl(i, this).m_max_reach_nodes; // make a copy, to prevent it from changing while we iterate over it
                for (node_set::iterator it = nodes.begin(); it != nodes.end(); ++it) {
                    unsigned chosen_node_id = *it;
                    if ((chosen_node_id > fixed_node_id) || ((i > fixed_pos) && (chosen_node_id == fixed_node_id))) {
                        // Don't use any nodes newer than the fixed node; we'll have a chance to use newer nodes when they are taken off the worklist later.
                        // Furthermore, don't use the fixed node further along that the fixed position; we'll have a chance to use it in both places when the fixed position advances.
                        // Note that iterating over the max_reach_nodes set return nodes in ascending order, so we can bail out here.
                        break;
                    }
                    chosen_nodes.push_back(chosen_node_id);
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    unsigned num_cond_vars_pushed = 0;
#else
                    scoped_push _push1(m_solver);
#endif
                    cube_t const& pos_cube = m_nodes[chosen_node_id].m_cube;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    expr_ref_vector const& body_pred_cond_vars = info.m_body_pred_cond_vars[i];
                    unsigned num_preds = body_pred_cond_vars.size();
#else
                    expr_ref_vector const& body_preds = info.m_body_preds[i];
                    unsigned num_preds = body_preds.size();
#endif
                    CASSERT("predabst", num_preds == pos_cube.size());
                    for (unsigned i = 0; i < num_preds; ++i) {
                        if (pos_cube[i]) {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                            num_cond_vars_pushed++;
                            cond_vars.push_back(body_pred_cond_vars[i]);
#else
                            m_stats.m_num_solver_assert_invocations++;
                            m_solver.assert_expr(body_preds[i]);
#endif
                        }
                    }

                    m_stats.m_num_solver_check_body_invocations++;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    lbool result = info.m_rule_solver->check(cond_vars.size(), cond_vars.c_ptr());
#else
                    lbool result = m_solver.check();
#endif
                    if (result == l_false) {
                        // unsat body
                        STRACE("predabst", tout << "Applying rule " << ri << " to nodes ("; reorder_output_nodes(tout, chosen_nodes, positions); tout << ") failed\n";);
                        m_stats.m_num_rules_failed++;
                    }
                    else {
                        cart_pred_abst_rule(ri, fixed_pos, fixed_node_id, positions, chosen_nodes, cond_vars);
                    }

#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                    for (unsigned i = 0; i < num_cond_vars_pushed; ++i) {
                        cond_vars.pop_back();
                    }
#endif
                    chosen_nodes.pop_back();
                }
            }
            else {
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
                CASSERT("predabst", info.m_rule_solver->check(cond_vars.size(), cond_vars.c_ptr()) != l_false);
#else
                CASSERT("predabst", m_solver.check() != l_false);
#endif

                // collect abstract cube
                cube_t cube = cart_pred_abst_cube(ri, cond_vars);
                STRACE("predabst", tout << "Applying rule " << ri << " to nodes (" << chosen_nodes << ") succeeded, with cube [" << cube << "]\n";);
                m_stats.m_num_rules_succeeded++;

                // add and check the node
                node_info const* node = add_node(ri, cube, reorder_nodes(chosen_nodes, positions));
                if (node) {
                    check_node_property(*node);
                }
            }
        }

        cube_t cart_pred_abst_cube(rule_info const& ri, expr_ref_vector& cond_vars) {
            rule_instance_info const& info = ri.m_instance_info;
#ifdef PREDABST_ASSERT_EXPR_UPFRONT
            expr_ref_vector const& es = info.m_head_pred_cond_vars;
#else
            expr_ref_vector const& es = info.m_head_preds;
#endif
            unsigned num_preds = es.size();
            cube_t cube;
            cube.resize(num_preds);
#ifdef PREDABST_COMPLETE_CUBE
            for (unsigned i = 0; i < num_preds; ++i) {
                cube[i] = is_implied(es.get(i), info, cond_vars);
            }
#else
            func_decl_info const& fi = ri.get_decl(this);
            build_cube(cube, es, fi.m_preds, fi.m_root_preds, info, cond_vars);
#endif
            return cube;
        }

        void check_node_property(node_info const& node) {
            if (node.m_fdecl_info.m_is_output_predicate) {
                STRACE("predabst", tout << "Reached query symbol " << node.m_fdecl_info << "\n";);
                throw acr_error(node.m_id, reached_query);
            }
            if (node.m_fdecl_info.m_has_template) {
                STRACE("predabst", tout << "Template instance for " << node.m_fdecl_info << " doesn't satisfy rule\n";);
                throw acr_error(node.m_id, bad_template);
            }
            if (node.m_fdecl_info.m_is_wf_predicate) {
                if (!is_well_founded(node)) {
                    STRACE("predabst", tout << "Formula is not well-founded\n";);
                    throw acr_error(node.m_id, not_wf);
                }
            }
        }

        bool is_well_founded(node_info const& node) {
            func_decl_info const& fi = node.m_fdecl_info;
            CASSERT("predabst", fi.m_is_wf_predicate);

            expr_ref expr = cube_to_formula(node.m_cube, fi.m_preds);
            expr_ref_vector args = get_fresh_args(fi.m_fdecl, "s");
            expr_ref to_rank = apply_subst(expr, build_subst(fi.m_vars, args));

            return well_founded(args, to_rank, NULL, NULL);
        }

        node_info const* add_node(rule_info const& ri, cube_t const& cube, node_vector const& nodes = node_vector()) {
            func_decl_info& fi = ri.get_decl(this);
            // first fixpoint check combined with maximality maintainance
            node_vector old_lt_nodes;
            for (node_set::iterator it = fi.m_max_reach_nodes.begin(); it != fi.m_max_reach_nodes.end(); ++it) {
                cube_t const& old_cube = m_nodes[*it].m_cube;
                // if cube implies existing cube then nothing to add
                if (cube_leq(cube, old_cube, fi)) {
                    STRACE("predabst", tout << "New node is subsumed by node " << *it << " with cube [" << old_cube << "]\n";);
                    CASSERT("predabst", old_lt_nodes.empty());
                    m_stats.m_num_nodes_suppressed++;
                    return NULL;
                }
                // stronger old cubes will not be considered maximal
                if (cube_leq(old_cube, cube, fi)) {
                    STRACE("predabst", tout << "New node subsumes node " << *it << " with cube [" << old_cube << "]\n";);
                    old_lt_nodes.push_back(*it);
                }
            }
            // (no???) fixpoint reached since didn't return
            // remove subsumed maximal nodes
            for (node_vector::iterator it = old_lt_nodes.begin(); it != old_lt_nodes.end(); ++it) {
                m_stats.m_num_nodes_subsumed++;
                fi.m_max_reach_nodes.remove(*it);
                m_node_worklist.remove(*it); // removing non-existent element is ok
            }
            // no fixpoint reached hence create new node
            m_stats.m_num_nodes_created++;
            m_nodes.push_back(node_info(m_nodes.size(), fi, cube, ri.m_id, nodes));
            node_info const& node = m_nodes.back();
            fi.m_max_reach_nodes.insert(node.m_id);
            m_node_worklist.insert(node.m_id);
            STRACE("predabst", tout << "Added node " << node << " for " << fi << "\n";);
            return &node;
        }

        bool not_reachable_without_abstraction(node_info const& root_node, expr_ref_vector const& root_args, core_tree_info& core_info) const {
            STRACE("predabst", tout << "Determining reachability of node " << root_node << " without abstraction\n";);
            bool result = mk_core_tree(root_node, root_args, core_info);
            STRACE("predabst", tout << "Node " << root_node << " is " << (result ? "not " : "") << "reachable without abstraction\n";);
            return result;
        }

        bool refine_predicates_not_reachable(expr_ref_vector const& root_args, core_tree_info const& core_info) {
            expr_ref last_clause_body(m);
            core_clauses clauses = mk_core_clauses(root_args, core_info, &last_clause_body);
            core_clauses clauses2 = cone_of_influence(clauses, last_clause_body);
            core_clause_solutions solutions = solve_core_clauses(clauses2);
            return refine_preds(solutions, core_info.m_name2func_decl);
        }

        bool good_template_without_abstraction(node_info const& root_node, expr_ref_vector const& root_args, core_tree_template_info& core_template_info) const {
            STRACE("predabst", tout << "Determining template implication for node " << root_node << " without abstraction\n";);
            func_decl_info const& fi = root_node.m_fdecl_info;
            CASSERT("predabst", fi.m_has_template);
            template_info const& temp = m_templates[fi.m_template_id];
            expr_ref actual_cube = mk_leaves(root_node, root_args);
            smt_params new_param;
            smt::kernel solver(m, new_param);
            solver.assert_expr(actual_cube);
            core_template_info.m_body = mk_conj(apply_subst(temp.m_body, get_temp_subst_vect(temp, root_args)));
            expr_ref e(m.mk_not(core_template_info.m_body), m);
            solver.assert_expr(e);
            bool result = (solver.check() == l_false);
            STRACE("predabst", tout << "Node " << root_node << " does " << (result ? "" : "not ") << "imply the template instance without abstraction\n";);
            return result;
        }

        bool refine_predicates_good_template(expr_ref_vector const& root_args, core_tree_info const& core_info, core_tree_template_info const& core_template_info) {
            core_clauses clauses = mk_core_clauses(root_args, core_info);
            bool result = false;
            expr_ref e(m.mk_not(core_template_info.m_body), m);
            if (false /*m_fp_params.solve_clauses_dnf()*/) { // >>>
                expr_ref_vector disjs = get_disj_terms(to_dnf(e));
                for (unsigned i = 0; i < disjs.size(); ++i) {
                    expr_ref disj(disjs.get(i), m);
                    core_clauses clauses2 = cone_of_influence_with_extra(clauses, disj);
                    core_clause_solutions solutions = solve_core_clauses(clauses2);
                    result |= refine_preds(solutions, core_info.m_name2func_decl);
                }
            }
            else {
                core_clauses clauses2 = cone_of_influence_with_extra(clauses, e);
                core_clause_solutions solutions = solve_core_clauses(clauses2);
                result |= refine_preds(solutions, core_info.m_name2func_decl);
            }
            return result;
        }

        bool wf_without_abstraction(node_info const& root_node, expr_ref_vector const& root_args, core_tree_wf_info& core_wf_info) const {
            STRACE("predabst", tout << "Determining well-foundedness of node " << root_node << " without abstraction\n";);
            CASSERT("predabst", root_node.m_fdecl_info.m_is_wf_predicate);
            expr_ref actual_cube = mk_leaves(root_node, root_args);
            quantifier_elimination(root_args, actual_cube);
            bool result = well_founded(root_args, actual_cube, &core_wf_info.m_bound, &core_wf_info.m_decrease);
            STRACE("predabst", tout << "Node " << root_node << " is " << (result ? "" : "not ") << "well-founded without abstraction\n";);
            return result;
        }

        bool refine_predicates_wf(expr_ref_vector const& root_args, core_tree_info const& core_info, core_tree_wf_info const& core_wf_info) {
            core_clauses clauses = mk_core_clauses(root_args, core_info);
            bool result = false;
            core_clauses bound_clauses = cone_of_influence_with_extra(clauses, core_wf_info.m_bound);
            core_clause_solutions bound_solutions = solve_core_clauses(bound_clauses);
            result |= refine_preds(bound_solutions, core_info.m_name2func_decl);
            core_clauses decrease_clauses = cone_of_influence_with_extra(clauses, core_wf_info.m_decrease);
            core_clause_solutions decrease_solutions = solve_core_clauses(decrease_clauses);
            result |= refine_preds(decrease_solutions, core_info.m_name2func_decl);
            return result;
        }

        bool refine_preds(core_clause_solutions const& solutions, vector<func_decl_info*> const& name2func_decl) {
            unsigned new_preds_added = 0;
            for (unsigned i = 0; i < solutions.size(); ++i) {
                core_clause_solution const& solution = solutions.get(i);
                CASSERT("predabst", solution.m_head.m_name < name2func_decl.size());
                func_decl_info& fi = *name2func_decl[solution.m_head.m_name];
                CASSERT("predabst", !fi.m_is_output_predicate);
                if (!fi.m_has_template) {
                    expr_ref pred(replace_pred(solution.m_head.m_args, fi.m_vars, solution.m_body), m);
                    new_preds_added += maybe_add_pred(fi, pred);
                }
            }
            return (new_preds_added > 0);
        }

        static bool contains_pred(vector<pred_info> const& preds, expr_ref const& pred) {
            for (vector<pred_info>::const_iterator it = preds.begin(); it != preds.end(); ++it) {
                if (it->m_pred == pred) {
                    return true;
                }
            }
            return false;
        }

        unsigned maybe_add_pred(func_decl_info& fi, expr_ref const& pred) {
            if (m.is_true(pred) || m.is_false(pred)) {
                STRACE("predabst", tout << "Ignoring predicate " << mk_pp(pred, m) << " for " << fi << "(" << fi.m_vars << ")\n";);
                return 0;
            }
            else if (contains_pred(fi.m_preds, pred)) {
                STRACE("predabst", tout << "Predicate " << mk_pp(pred, m) << " for " << fi << "(" << fi.m_vars << ") is already present\n";);
                return 0;
            }
            else {
                STRACE("predabst", tout << "Found new predicate " << mk_pp(pred, m) << " for " << fi << "(" << fi.m_vars << ")\n";);
                fi.m_preds.push_back(pred_info(pred));
                return 1;
            }
        }

        void constrain_templates(node_info const& error_node, expr_ref_vector const& error_args, acr_error_kind error_kind) {
            expr_ref cs = mk_leaves(error_node, error_args, false);
            quantifier_elimination(vector_concat(error_args, m_template_params), cs);

            expr_ref to_solve(m);
            if (error_kind == reached_query) {
                STRACE("predabst", tout << "Refining templates (reached query)\n";);
                to_solve = template_constraint_reached_query(cs);
            }
            else if (error_kind == bad_template) {
                STRACE("predabst", tout << "Refining templates (bad template)\n";);
                to_solve = template_constraint_bad_template(error_node, error_args, cs);
            }
            else {
                CASSERT("predabst", error_kind == not_wf);
                STRACE("predabst", tout << "Refining templates (not well-founded)\n";);
                to_solve = template_constraint_not_wf(error_args, cs);
            }

            m_template_constraints.push_back(to_solve);
            m_template_constraint_vars.append(error_args);
        }

        expr_ref template_constraint_reached_query(expr_ref cs) {
            return expr_ref(m.mk_not(cs), m);
        }

        expr_ref template_constraint_bad_template(node_info const& node, expr_ref_vector const& args, expr_ref cs) {
            template_info const& temp = m_templates[node.m_fdecl_info.m_template_id];
            expr_ref_vector temp_subst = get_temp_subst_vect_noparams(temp, args);
            expr_ref body = mk_conj(apply_subst(temp.m_body, temp_subst));
            return expr_ref(m.mk_or(m.mk_not(cs), body), m);
        }

        expr_ref template_constraint_not_wf(expr_ref_vector const& args, expr_ref cs) {
            expr_ref bound(m);
            expr_ref decrease(m);
            well_founded_bound_and_decrease(args, bound, decrease);
            return expr_ref(m.mk_or(m.mk_not(cs), m.mk_and(bound, decrease)), m);
        }

        bool mk_core_tree(node_info const& root_node, expr_ref_vector const& root_args, core_tree_info &core_info) const {
            smt_params new_param;
            smt::kernel solver(m, new_param);
            core_tree& core = core_info.m_core;
            vector<func_decl_info*>& name2func_decl = core_info.m_name2func_decl;

            vector<name_app> todo;
            todo.push_back(name_app(0, root_args));
            core.push_back(core_tree_node(root_node.m_id));
            name2func_decl.push_back(&root_node.m_fdecl_info);

            while (!todo.empty()) {
                name_app item = todo.back();
                todo.pop_back();

                core[item.m_name].m_visited = true;

                node_info const& node = m_nodes[core[item.m_name].m_node_id];
                rule_info const& ri = m_rules[node.m_parent_rule];

                STRACE("predabst", tout << "To reach node " << node << " / tree node " << item.m_name << " (" << node.m_fdecl_info << "(" << item.m_args << ")) via rule " << node.m_parent_rule << " requires:\n";);
                expr_ref_vector rule_subst(m);
                expr_ref_vector terms = get_rule_terms(ri.m_rule, item.m_args, rule_subst);
                for (unsigned i = 0; i < terms.size(); ++i) {
                    STRACE("predabst", tout << "  " << mk_pp(terms.get(i), m) << "\n";);
                    solver.assert_expr(terms.get(i));
                    if (solver.check() != l_true) {
                        core_info.m_last_name = item.m_name;
                        core_info.m_last_pos = i;
                        return true;
                    }
                }
                for (unsigned i = 0; i < ri.get_tail_size(); ++i) {
                    node_info const& qnode = m_nodes[node.m_parent_nodes[i]];
                    unsigned qname = core.size();
                    expr_ref_vector qargs = apply_subst(ri.get_args(i), rule_subst);
                    STRACE("predabst", tout << "  reaching node " << qnode << " / tree node " << qname << " (" << qnode.m_fdecl_info << "(" << qargs << "))\n";);
                    todo.push_back(name_app(qname, qargs));
                    core.push_back(core_tree_node(qnode.m_id));
                    core[item.m_name].m_names.push_back(qname);
                    name2func_decl.push_back(&qnode.m_fdecl_info);
                }
            }

            STRACE("predabst", {
                lbool result = solver.check();
                CASSERT("predabst", result == l_true);
                model_ref modref;
                solver.get_model(modref);
                expr_ref_vector solution(m);
                for (unsigned i = 0; i < root_args.size(); ++i) {
                    expr_ref val(m);
                    if (modref->eval(root_args.get(i), val, true)) {
                        tout << "Failed to get model for root_args[" << i << "]\n";
                    }
                    solution.push_back(val);
                }
                tout << "Example solution: " << root_node.m_fdecl_info << "(" << solution << ")\n";
            });

            core_info.m_last_name = (unsigned)-1;
            core_info.m_last_pos = 0;
            return false;
        }

        core_clauses mk_core_clauses(expr_ref_vector const& root_args, core_tree_info const& core_info, expr_ref* last_clause_body = NULL) const {
            STRACE("predabst", tout << "Building clauses\n";);
            core_clauses clauses;

            unsigned last_name = core_info.m_last_name;
            unsigned last_pos = core_info.m_last_pos;
            core_tree const& core = core_info.m_core;

            vector<name_app> todo;
            todo.push_back(name_app(0, root_args));

            bool found_last = false;
            while (!found_last && !todo.empty()) {
                name_app item = todo.back();
                todo.pop_back();

                vector<name_app> parents;

                if (item.m_name == last_name) {
                    found_last = true;
                }

                expr_ref_vector cs(m);

                node_info const& node = m_nodes[core[item.m_name].m_node_id];
                vector<unsigned> const& names = core[item.m_name].m_names;
                rule_info const& ri = m_rules[node.m_parent_rule];

                expr_ref_vector rule_subst(m);
                expr_ref_vector terms = get_rule_terms(ri.m_rule, item.m_args, rule_subst);
                for (unsigned i = 0; i < (found_last ? last_pos + 1 : terms.size()); ++i) {
                    cs.push_back(terms.get(i));
                }

                if (found_last) {
                    CASSERT("predabst", last_clause_body); // found_last => last_clause_body
                    *last_clause_body = cs.get(cs.size() - 1);
                    CASSERT("predabst", names.empty());
                }
                else {
                    CASSERT("predabst", names.size() == ri.get_tail_size());
                    for (unsigned i = 0; i < ri.get_tail_size(); ++i) {
                        node_info const& qnode = m_nodes[node.m_parent_nodes[i]];
                        unsigned qname = names.get(i);
                        if (!core[qname].m_visited) {
                            continue;
                        }
                        // Ensure that all the qargs are (distinct) uninterpreted constants.
                        expr_ref_vector pargs = apply_subst(ri.get_args(i), rule_subst);
                        expr_ref_vector qargs(m);
                        for (unsigned j = 0; j < pargs.size(); ++j) {
                            expr_ref arg_j(pargs.get(j), m);
                            if (is_uninterp_const(arg_j) && !qargs.contains(arg_j)) {
                                qargs.push_back(arg_j);
                            }
                            else {
                                app_ref f(m.mk_fresh_const("x", get_sort(arg_j)), m);
                                qargs.push_back(f);
                                expr_ref constraint(m.mk_eq(f, arg_j), m);
                                cs.push_back(constraint);
                            }
                        }
                        todo.push_back(name_app(qname, qargs));
                        parents.push_back(name_app(qname, qargs));
                    }
                }

                core_clause clause(item, cs, parents);
                STRACE("predabst", tout << "Adding clause for " << node.m_fdecl_info << ": " << clause << "\n";);
                clauses.push_back(clause);
            }

            CASSERT("predabst", !last_clause_body || found_last); // last_clause_body => found_last
            return clauses;
        }

        core_clauses cone_of_influence(core_clauses const& clauses, expr_ref const& critical) const {
            if (false /*!m_fp_params.use_cone_of_influence()*/) { // >>>
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

        vector<unsigned> get_farkas_coeffs(proof_ref const& pr) const {
            iz3mgr i(m);
            iz3mgr::ast p(&m, pr.get());
            iz3mgr::pfrule dk = i.pr(p);
            if (dk == PR_TH_LEMMA &&
                i.get_theory_lemma_theory(p) == iz3mgr::ArithTheory &&
                i.get_theory_lemma_kind(p) == iz3mgr::FarkasKind) {
                std::vector<rational> rat_coeffs;
                i.get_farkas_coeffs(p, rat_coeffs);
                vector<unsigned> coeffs;
                for (unsigned i = 0; i < rat_coeffs.size(); ++i) {
                    coeffs.push_back(rat_coeffs[i].get_unsigned());
                }
                STRACE("predabst", tout << "Proof kind is Farkas, with coefficients " << coeffs << "\n";);
                return coeffs;
            }
            else {
                STRACE("predabst", tout << "Proof kind is not Farkas\n";);
                return vector<unsigned>();
            }
        }

        expr_ref clauses_to_iz3_interp_problem(core_clauses const& clauses) const {
            expr_ref_vector name2node(m);
            for (unsigned i = 0; i < clauses.size(); ++i) {
                unsigned j = clauses.size() - 1 - i;
                core_clause const& clause = clauses[j];
                expr_ref_vector conjs(m);
                conjs.append(clause.m_interp_body);
                for (unsigned k = 0; k < clause.m_uninterp_body.size(); ++k) {
                    conjs.push_back(name2node.get(clause.m_uninterp_body[k].m_name));
                }
                name2node.reserve(clause.m_head.m_name + 1);
                name2node[clause.m_head.m_name] = expr_ref(m.mk_interp(mk_conj(conjs)), m);
            }
            return expr_ref(name2node.get(0), m);
        }

        core_clause_solutions solve_core_clauses_iz3(core_clauses const& clauses) const {
            proof_gen_mode old_pgm = m.proof_mode();
            m.toggle_proof_mode(PGM_FINE);
            params_ref params;
            solver* s = mk_smt_solver(m, params, symbol::null); // or "QF_LIA"?
            expr_ref tree = clauses_to_iz3_interp_problem(clauses);
            STRACE("predabst", tout << "Interpolation problem: " << mk_pp(tree, m) << "\n";);
            ptr_vector<ast> cnsts;
            ptr_vector<ast> interps;
            interpolation_options_struct opts;
            //>>>opts.set("weak", "1");
            lbool result = iz3interpolate(m,
                *s,
                tree,
                cnsts,
                interps,
                model_ref(),
                &opts);
            dealloc(s);

            STRACE("predabst", {
                tout << "Interpolants:\n";
                for (unsigned i = 0; i < interps.size(); ++i) {
                    tout << "  " << i << ": " << mk_pp(interps.get(i), m) << "\n";
                }
            });

            core_clause_solutions solutions;
            for (unsigned i = clauses.size() - 1; i > 0; --i) { // skip clause 0
                core_clause const& clause = clauses[i];
                if (i < interps.size()) {
                    expr_ref body(to_expr(interps.get(clauses.size() - 1 - i)), m);
                    core_clause_solution solution(clause.m_head, body);
                    STRACE("predabst", tout << "Solution for clause " << i << ": " << solution << "\n";);
                    solutions.push_back(solution);
                }
            }

            for (unsigned i = 0; i < cnsts.size(); ++i) {
                m.dec_ref(cnsts[i]);
            }
            for (unsigned i = 0; i < interps.size(); ++i) {
                m.dec_ref(interps[i]);
            }
            m.toggle_proof_mode(old_pgm);
            return solutions;
        }

        core_clause_solutions solve_core_clauses_non_iz3(core_clauses const& clauses) const {
            proof_gen_mode old_pgm = m.proof_mode();
            m.toggle_proof_mode(PGM_FINE);
            smt_params new_param;
            smt::kernel solver(m, new_param);
            unsigned num_assertions = 0;
            vector<unsigned> assertion_start_index;
            for (unsigned i = 0; i < clauses.size(); ++i) {
                assertion_start_index.push_back(num_assertions);
                core_clause const& clause = clauses[i];
                for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
                    solver.assert_expr(clause.m_interp_body[j]);
                    ++num_assertions;
                }
            }
            lbool result = solver.check();
            CASSERT("predabst", result == l_false);

            proof_ref pr(solver.get_proof(), m);
            m.toggle_proof_mode(old_pgm);
            vector<unsigned> clause_coeffs = get_farkas_coeffs(pr);
            if (clause_coeffs.empty()) {
                STRACE("predabst", tout << "Cannot solve clauses: not a Farkas-style proof\n";);
                return core_clause_solutions();
            }

            core_clause_solutions solutions;
            expr_ref_vector name2solution(m);
            for (unsigned i = clauses.size() - 1; i > 0; --i) { // skip clause 0
                core_clause const& clause = clauses[i];
                vector<unsigned> coeffs;
                expr_ref_vector inequalities(m);
                for (unsigned j = 0; j < clause.m_interp_body.size(); ++j) {
                    coeffs.push_back(clause_coeffs[assertion_start_index[i] + j]);
                    inequalities.push_back(clause.m_interp_body[j]);
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

        core_clause_solutions solve_core_clauses(core_clauses const& clauses) const {
            if (true /* && m_fp_params.use_iz3_interpolation() */) {
                return solve_core_clauses_iz3(clauses);
            }
            else {
                return solve_core_clauses_non_iz3(clauses);
            }
        }

        expr_ref mk_leaves(node_info const& root_node, expr_ref_vector const& root_args, bool substitute_template_params = true) const {
            STRACE("predabst", tout << "Determining reachability criterion for node " << root_node << " without abstraction\n";);
            expr_ref_vector cs(m);

            struct todo_item {
                unsigned        m_node_id;
                expr_ref_vector m_args;
                todo_item(unsigned node_id, expr_ref_vector const& args) :
                    m_node_id(node_id),
                    m_args(args) {}
            };
            vector<todo_item> todo;
            todo.push_back(todo_item(root_node.m_id, root_args));

            while (!todo.empty()) {
                todo_item item = todo.back();
                todo.pop_back();

                expr_ref_vector const& args = item.m_args;
                node_info const& node = m_nodes[item.m_node_id];
                rule_info const& ri = m_rules[node.m_parent_rule];

                STRACE("predabst", tout << "To reach node " << node << " (" << node.m_fdecl_info << "(" << args << ")) via rule " << ri << " requires:\n";);
                expr_ref_vector rule_subst(m);
                expr_ref_vector terms = get_rule_terms(ri.m_rule, args, rule_subst, substitute_template_params);
                STRACE("predabst", tout << "  " << mk_pp(mk_conj(terms), m) << "\n";);
                cs.append(terms);
                for (unsigned i = 0; i < ri.get_tail_size(); ++i) {
                    node_info const& qnode = m_nodes[node.m_parent_nodes[i]];
                    expr_ref_vector qargs = apply_subst(ri.get_args(i), rule_subst);
                    STRACE("predabst", tout << "  reaching node " << qnode << " (" << qnode.m_fdecl_info << "(" << qargs << "))\n";);
                    todo.push_back(todo_item(qnode.m_id, qargs));
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

            int max_lambda = 2;
            expr_ref_vector lambda_constraints = mk_bilinear_lambda_constraints(lambda_infos, max_lambda, m);

            STRACE("predabst", tout << "  constraints: " << constraints << "\n";);
            STRACE("predabst", tout << "  lambda constraint: " << lambda_constraints << "\n";);

            smt_params new_param;
            smt::kernel solver(m, new_param);
            if (m_template_extras) {
                solver.assert_expr(m_template_extras);
            }
            for (unsigned i = 0; i < constraints.size(); ++i) {
                solver.assert_expr(constraints.get(i));
            }
            for (unsigned i = 0; i < lambda_constraints.size(); ++i) {
                solver.assert_expr(lambda_constraints.get(i));
            }
            if (solver.check() != l_true) {
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

            return true;
        }

        void register_decl(model_ref const& md, func_decl* fdecl, expr* e) const {
            STRACE("predabst", tout << "Model for " << fdecl->get_name() << " is " << mk_pp(e, m) << "\n";);
            if (fdecl->get_arity() == 0) {
                md->register_decl(fdecl, e);
            }
            else {
                func_interp* fi = alloc(func_interp, m, fdecl->get_arity());
                fi->set_else(e);
                md->register_decl(fdecl, fi);
            }
        }

        void print_core_tree(std::ostream& out, core_tree const& core) {
            for (unsigned i = 0; i < core.size(); ++i) {
                out << "core_name: " << i << ", core_id: " << core[i].m_node_id << ", core_ids: [";
                for (unsigned j = 0; j < core[i].m_names.size(); ++j) {
                    out << " " << core[i].m_names.get(j);
                }
                out << "]\n";
            }
        }

        void print_proof_prolog(std::ostream& out, unsigned id) const {
            node_set todo_nodes;
            todo_nodes.insert(id);
            while (!todo_nodes.empty()) {
                unsigned curr_id = *todo_nodes.begin();
                todo_nodes.remove(curr_id);
                node_info const& node = m_nodes[curr_id];
                out << "hyper_resolve([" << node.m_parent_nodes << "], "
                    << node.m_parent_rule << ", " << curr_id << ")." << std::endl;
                for (unsigned i = 0; i < node.m_parent_nodes.size(); ++i) {
                    todo_nodes.insert(node.m_parent_nodes[i]);
                }
            }
        }

        void print_initial_state(std::ostream& out) const {
            out << "=====================================\n";
            out << "Initial state:\n";
            out << "  Symbols:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                     it != m_func_decl2info.end(); ++it) {
                out << "    " << it->m_key->get_name() << "(" << it->m_value->m_vars << ")";
                if (it->m_value->m_is_output_predicate) {
                    out << " is a query symbol" << std::endl;
                    CASSERT("predabst", it->m_value->m_users.empty());
                }
                else if (it->m_value->m_has_template) {
                    template_info const& temp = m_templates.get(it->m_value->m_template_id);
                    out << " has template " << *it->m_value << "(" << temp.m_vars << ") := " << temp.m_body << std::endl;
                    CASSERT("predabst", it->m_value->m_users.empty());
                }
                else {
                    out << " is used by rules " << it->m_value->m_users << std::endl;
                }
            }
            out << "  Rules:" << std::endl;
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                out << "    " << i << ": ";
                m_rules[i].m_rule->display_smt2(m, out);
                out << std::endl;
            }
            out << "=====================================\n";
        }

#ifndef PREDABST_COMPLETE_CUBE
        void print_preds_forest(std::ostream& out, vector<pred_info> const& preds, vector<unsigned> const& preds_idxs, std::string const& prefix) const {
            for (unsigned i = 0; i < preds_idxs.size(); ++i) {
                unsigned idx = preds_idxs[i];
                out << prefix << mk_pp(preds[idx].m_pred, m) << "\n";
                print_preds_forest(out, preds, preds[idx].m_implied, prefix + "  ");
            }
        }

        void print_preds_forest(std::ostream& out, func_decl_info const& fi) const {
            print_preds_forest(out, fi.m_preds, fi.m_root_preds, "");
        }
#endif

        void print_refinement_state(std::ostream& out, unsigned refine_count) const {
            out << "=====================================\n";
            out << "State before refinement step " << refine_count << ":\n";
            out << "  Symbols:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                it != m_func_decl2info.end(); ++it) {
                if (it->m_value->m_is_output_predicate ||
                    it->m_value->m_has_template) {
                    CASSERT("predabst", it->m_value->m_preds.empty());
                }
                else {
                    out << "    " << it->m_key->get_name() << "(" << it->m_value->m_vars << ") has ";
                    if (it->m_value->m_preds.empty()) {
                        out << "no ";
                    }
                    out << "predicates ";
                    for (vector<pred_info>::iterator it2 = it->m_value->m_preds.begin();
                        it2 != it->m_value->m_preds.end(); ++it2) {
                        out << mk_pp(it2->m_pred, m) << ", ";
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
                m_rules[i].m_instance_info.display(out, m_rules[i], this);
            }
            out << "=====================================\n";
        }

        void print_inference_state(std::ostream& out, unsigned refine_count, unsigned infer_count) const {
            out << "=====================================\n";
            out << "State before inference step " << refine_count << "." << infer_count << ":\n";
            out << "  Nodes:" << std::endl;
            for (unsigned i = 0; i < m_nodes.size(); ++i) {
                node_info const& node = m_nodes[i];
                out << "    " << i << ": rule " << node.m_parent_rule
                    << " applied to nodes (" << node.m_parent_nodes
                    << ") giving cube [" << node.m_cube
                    << "] for " << node.m_fdecl_info
                    << std::endl;
            }
            out << "  Max reached nodes:" << std::endl;
            for (obj_map<func_decl, func_decl_info*>::iterator it = m_func_decl2info.begin();
                it != m_func_decl2info.end(); ++it) {
                if (it->m_value->m_is_output_predicate) {
                    CASSERT("predabst", it->m_value->m_max_reach_nodes.num_elems() == 0);
                }
                else if (it->m_value->m_has_template) {
                    CASSERT("predabst", it->m_value->m_max_reach_nodes.num_elems() == 1);
                }
                else {
                    out << "    " << it->m_key->get_name() << ": "
                        << it->m_value->m_max_reach_nodes << std::endl;
                }
            }
            out << "  Worklist: " << m_node_worklist << std::endl;
            out << "=====================================\n";
        }

        void print_statistics(std::ostream& out) const {
            statistics st;
            collect_statistics(st);
            st.display(out);
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
