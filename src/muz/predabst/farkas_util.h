/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    farkas_util.h

Abstract:

    Utilities for applying farkas lemma over linear implications.

Author:

    Tewodros A. Beyene (t-tewbe) 2014-10-22.

Revision History:

--*/
#include "th_rewriter.h"
#include "smt2parser.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "arith_rewriter.h"
#include "ast_pp.h"
#include "smt_kernel.h"
#include "smt_params.h"
#include "model.h"
#include "model2expr.h"
#include "model_smt2_pp.h"
#include "ast_counter.h"
#include "var_subst.h"
#include <map>
#include "qe_lite.h"

struct core_clause {
    unsigned cl_name;
    expr_ref_vector cl_vars;
    expr_ref cl_body_as;
    expr_ref_vector cl_body_qs;

    core_clause(ast_manager m) : cl_vars(m), cl_body_as(m), cl_body_qs(m) {}

    core_clause(unsigned in_cl_name, expr_ref_vector in_cl_vars, expr_ref in_cl_body_as, expr_ref_vector in_cl_body_qs) :
        cl_name(in_cl_name), cl_vars(in_cl_vars), cl_body_as(in_cl_body_as), cl_body_qs(in_cl_body_qs) {
    }

    void display() {
        std::cout << "cl_name: " << cl_name << ", cl_vars: [";
        for (unsigned i = 0; i < cl_vars.size(); i++) {
            std::cout << " " << mk_pp(cl_vars.get(i), cl_body_as.m());
        }
        std::cout << "], cl_body_as : " << mk_pp(cl_body_as.get(), cl_body_as.m()) << ", cl_body_qs : [";
        for (unsigned i = 0; i < cl_body_qs.size(); i++) {
            std::cout << " " << mk_pp(cl_body_qs.get(i), cl_body_as.m());
        }
        std::cout << "]\n";
    }
};

typedef std::pair<unsigned, symbol> name2symbol;
typedef std::map<unsigned, std::pair<std::pair<unsigned, vector<unsigned> >, vector<unsigned> > > core_tree;
void display_core_tree(core_tree m_core_tree);

struct core_to_throw {
    unsigned root_id;
    unsigned last_name;
    unsigned last_node_tid;
    vector<unsigned> last_node_ids;
    unsigned pos;
    vector<name2symbol> name_map;
    core_tree core;

    core_to_throw(unsigned in_root_id, unsigned in_last_name, unsigned in_last_node_tid, vector<unsigned> in_last_node_ids, unsigned in_pos,
                  vector<name2symbol> in_name_map, core_tree in_core) {
        root_id = in_root_id;
        last_name = in_last_name;
        last_node_tid = in_last_node_tid;
        last_node_ids = in_last_node_ids;
        pos = in_pos;
        name_map = in_name_map;
        core = in_core;
    }

    void display() {
        std::cout << "root_id: " << root_id << ", last_name: " << last_name << ", last_id: " << last_node_tid << ", last_ids: [";
        for (unsigned i = 0; i < last_node_ids.size(); i++) {
            std::cout << " " << last_node_ids.get(i);
        }
        std::cout << "], critical pos: " << pos << "\n";
        std::cout << "name_map: [";
        for (unsigned i = 0; i < name_map.size(); i++) {
            std::cout << " " << name_map.get(i).first << "-" << name_map.get(i).second.str();
        }
        std::cout << "]\n";
        std::cout << "core size: " << core.size() << "\n";
        display_core_tree(core);
    }
};

typedef std::map<unsigned, std::pair<expr_ref_vector, std::pair<expr_ref, expr_ref_vector> > > core_clauses;
typedef vector<std::pair<symbol, std::pair<expr_ref_vector, std::pair<expr_ref, expr_ref_vector> > > > core_clauses2;

void display_core_clause(ast_manager& m, core_clauses clauses);
void display_core_clause2(ast_manager& m, core_clauses2 clauses);

void display_expr_ref_vector(expr_ref_vector& vect);

struct refine_pred_info {
    expr_ref pred;
    expr_ref_vector pred_vars;

    refine_pred_info(expr_ref in_pred, expr_ref_vector in_pred_vars) : pred_vars(in_pred_vars), pred(in_pred) {}

    void display() {
        std::cout << "pred: " << mk_pp(pred.get(), pred.m()) << ", pred_vars: [";
        for (unsigned i = 0; i < pred_vars.size(); i++) {
            std::cout << " " << mk_pp(pred_vars.get(i), pred.m());
        }
        std::cout << "]\n";
    }

    bool has_var(expr_ref arg) {
        return pred_vars.contains(arg);
    }
};

struct refine_cand_info {

    typedef vector<std::pair<symbol, vector<expr_ref_vector> > > refine_cand_rels_info;

    refine_cand_rels_info m_allrels_info;
    ast_manager& m;

    refine_cand_info(ast_manager& in_m) : m(in_m) {}
    void insert(symbol sym, expr_ref_vector args) {
        for (unsigned i = 0; i < m_allrels_info.size(); i++) {
            if (m_allrels_info.get(i).first == sym) {
                m_allrels_info.get(i).second.push_back(args);
                return;
            }
        }
        vector<expr_ref_vector> new_args;
        new_args.push_back(args);
        m_allrels_info.push_back(std::make_pair(sym, new_args));
    }

    void display() {
        for (unsigned i = 0; i < m_allrels_info.size(); i++) {
            std::cout << "refine_cand_info: " << i << ": " << m_allrels_info.get(i).first.str() << " -[ ";
            for (unsigned j = 0; j < m_allrels_info.get(i).second.size(); j++) {
                std::cout << "usage " << j << " -[ ";
                for (unsigned k = 0; k < m_allrels_info.get(i).second.get(j).size(); k++) {
                    std::cout << mk_pp(m_allrels_info.get(i).second.get(j).get(k), m) << " ";
                }
                std::cout << " ] ";
            }
            std::cout << " ] \n";
        }
    }

    refine_cand_rels_info get_info() {
        return m_allrels_info;
    }
};

template<class T>
static void push_front(vector<T>& v, T e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

static void push_front_0(expr_ref_vector& v, expr_ref e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

typedef enum { bilin_sing, bilin, lin } lambda_kind_sort;

typedef enum { reach, wf } acr_error_kind;

struct lambda_kind {
    expr_ref m_lambda;
    lambda_kind_sort m_kind;
    unsigned m_op;
    int m_lower_bound;
    int m_upper_bound;

    lambda_kind(expr_ref in_lambda, lambda_kind_sort in_kind, unsigned in_op) :
        m_lambda(in_lambda), m_kind(in_kind), m_op(in_op),
        m_lower_bound(0),
        m_upper_bound(0) {
    }
};

static expr_ref_vector get_all_terms(expr_ref term) {
    expr_ref_vector all_facts(term.m());
    if (!arith_util(term.m()).is_mul(term.get())) {
        all_facts.push_back(term);
    }
    else {
        expr_ref_vector facts(term.m());
        facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        for (unsigned i = 0; i < facts.size(); ++i) {
            all_facts.append(get_all_terms(expr_ref(facts[i].get(), term.m())));
        }
    }
    return all_facts;
}

static void get_all_terms(expr_ref term, expr_ref_vector vars, expr_ref_vector& var_facts, expr_ref_vector& const_facts, bool& has_params) {
    if (!arith_util(term.m()).is_mul(term.get())) {
        if (vars.contains(term)) {
            var_facts.push_back(term);
        }
        else {
            const_facts.push_back(term);
            // params check ***
            if (!arith_util(term.m()).is_numeral(term)) {
                has_params = true;
            }
        }
    }
    else {
        expr_ref_vector facts(term.m());
        facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        for (unsigned i = 0; i < facts.size(); ++i) {
            get_all_terms(expr_ref(facts[i].get(), term.m()), vars, var_facts, const_facts, has_params);
        }
    }
}

void get_interpolant_pred(expr_ref_vector args, expr_ref_vector vars, vector<refine_pred_info> interpolants, expr_ref_vector& in_pred);

void get_conj_terms(expr_ref conj, expr_ref_vector& terms);

void print_node_info(unsigned added_id, func_decl* sym, vector<bool> cube, unsigned r_id, vector<unsigned> parent_nodes);

class farkas_pred {
    expr_ref_vector m_vars;
    expr_ref_vector m_coeffs;
    unsigned m_op;
    expr_ref m_const;

    bool m_has_params;
    ast_manager& m_pred_manager;

public:

    farkas_pred(expr_ref_vector vars) : m_vars(vars), m_coeffs(vars.get_manager()),
        m_const(vars.get_manager()), m_op(1), m_has_params(false),
        m_pred_manager(vars.get_manager()) {
    }

    farkas_pred(expr_ref_vector vars, expr_ref_vector in_coeffs, unsigned in_op, expr_ref in_const) :
        m_vars(vars), m_coeffs(in_coeffs),
        m_const(in_const), m_op(in_op), m_has_params(false),
        m_pred_manager(vars.get_manager()) {
    }

    void put(expr_ref term) {
        arith_util arith(term.m());
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            m_coeffs.push_back(arith.mk_numeral(rational(0), true));
        }
        if (term.m().is_true(term)) {
            m_op = 1;
            m_const = arith.mk_numeral(rational(0), true);
        }
        else if (term.m().is_false(term)) {
            m_op = 1;
            m_const = arith.mk_numeral(rational(-1), true);
        }
        else {
            set(term);
        }
    }

    expr_ref_vector get_coeffs() {
        return m_coeffs;
    }

    expr_ref get_coeffs(unsigned i) {
        return expr_ref(m_coeffs.get(i), m_pred_manager);
    }

    unsigned get_op() {
        return m_op;
    }

    expr_ref get_const() {
        return m_const;
    }

    bool has_params() {
        return m_has_params;
    }

    void display() {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (i == 0) {
                std::cout << mk_pp(m_coeffs[i].get(), m_pred_manager) << " * " << mk_pp(m_vars[i].get(), m_pred_manager);
            }
            else {
                std::cout << " + " << mk_pp(m_coeffs[i].get(), m_pred_manager) << " * " << mk_pp(m_vars[i].get(), m_pred_manager);
            }
        }
        switch (m_op) {
        case 0:
            std::cout << " = ";
            break;
        case 1:
            std::cout << " =< ";
            break;
        case 2:
            std::cout << " >= ";
            break;
        case 3:
            std::cout << " < ";
            break;
        case 4:
            std::cout << " > ";
            break;
        default:
            std::cout << " Unknown relation! ";
            break;
        }
        std::cout << mk_pp(m_const.get(), m_pred_manager) << "\n";
        std::cout << "Params? : " << (m_has_params ? "TRUE" : "FALSE") << "\n";
    }

private:

    void rewrite_pred(expr_ref& term) {
        arith_util arith(term.m());
        expr *e1, *e2;
        if (term.m().is_eq(term, e1, e2)) {
            term = arith.mk_sub(e1, e2);
            m_op = 0;
        }
        else if (arith.is_le(term, e1, e2)) {
            term = arith.mk_sub(e1, e2);
        }
        else if (arith.is_ge(term, e1, e2)) {
            term = arith.mk_sub(e2, e1);
        }
        else if (arith.is_lt(term, e1, e2)) {
            term = arith.mk_sub(arith.mk_sub(e1, e2), arith.mk_numeral(rational(-1), true));
        }
        else if (arith.is_gt(term, e1, e2)) {
            term = arith.mk_sub(arith.mk_sub(e2, e1), arith.mk_numeral(rational(-1), true));
        }
        else {
            std::cout << "after subst fml: " << mk_pp(term, term.m()) << "\n";
            std::cout << "Unable to recognize predicate \n";
            throw(term);
        }
        th_rewriter rw(term.m());
        rw(term);
    }

    void set(expr_ref& term) {
        arith_util arith(m_pred_manager);
        rewrite_pred(term);
        expr_ref_vector p_coeffs(m_pred_manager), p_vars(m_pred_manager), p_const_facts(m_pred_manager), add_facts(m_pred_manager);
        if (arith.is_add(term.get())) {
            add_facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        }
        else {
            add_facts.push_back(term);
        }
        for (unsigned i = 0; i < add_facts.size(); ++i) {
            expr_ref_vector mul_facts(m_pred_manager), var_mul_facts(m_pred_manager), const_mul_facts(m_pred_manager);
            expr_ref mul_term(add_facts[i].get(), m_pred_manager);
            get_all_terms(mul_term, m_vars, var_mul_facts, const_mul_facts, m_has_params);
            SASSERT(var_mul_facts.size() <= 1);
            if (var_mul_facts.size() == 0) {
                p_const_facts.push_back(add_facts[i].get());
            }
            else if (const_mul_facts.size() == 0) {
                p_vars.push_back(add_facts[i].get());
                p_coeffs.push_back(arith.mk_numeral(rational(1), true));
            }
            else if (const_mul_facts.size() == 1) {
                p_vars.push_back(var_mul_facts[0].get());
                p_coeffs.push_back(const_mul_facts[0].get());
            }
            else {
                p_vars.push_back(var_mul_facts[0].get());
                p_coeffs.push_back(arith.mk_mul(const_mul_facts.size(), const_mul_facts.c_ptr()));
            }
        }
        if (p_const_facts.size() == 0) {
            m_const = arith.mk_numeral(rational(0), true);
        }
        else if (p_const_facts.size() == 1) {
            m_const = arith.mk_uminus(p_const_facts[0].get());
        }
        else {
            m_const = arith.mk_uminus(arith.mk_add(p_const_facts.size(), p_const_facts.c_ptr()));
        }
        th_rewriter rw(m_pred_manager);
        rw(m_const);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            for (unsigned j = 0; j < p_vars.size(); ++j) {
                if (m_vars[i].get() == p_vars[j].get()) {
                    m_coeffs.set(i, p_coeffs[j].get());
                    p_vars.erase(j);
                    p_coeffs.erase(j);
                    break;
                }
            }
        }
    }
};

class farkas_conj {
    expr_ref_vector m_vars;
    vector<expr_ref_vector> m_set_coeffs;
    vector<unsigned> m_set_op;
    vector<expr_ref> m_set_const;

    unsigned m_param_pred_count;
    ast_manager m_conj_manager;


public:
    farkas_conj(expr_ref_vector vars) :
        m_vars(vars), m_param_pred_count(0), m_conj_manager(vars.get_manager()) {
    }

    void add(farkas_pred& f_pred) {
        if (m_set_coeffs.size() == 0) {
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                expr_ref_vector init_coeff(m_conj_manager);
                init_coeff.push_back(f_pred.get_coeffs(i));
                m_set_coeffs.push_back(init_coeff);
            }
            m_set_op.push_back(f_pred.get_op());
            m_set_const.push_back(f_pred.get_const());
            if (f_pred.has_params()) {
                m_param_pred_count++;
            }
        }
        else {
            if (f_pred.has_params()) {
                for (unsigned i = 0; i < m_vars.size(); ++i) {
                    push_front_0(m_set_coeffs[i], f_pred.get_coeffs(i));
                }
                push_front(m_set_op, f_pred.get_op());
                push_front(m_set_const, f_pred.get_const());
                m_param_pred_count++;
            }
            else {
                for (unsigned i = 0; i < m_vars.size(); ++i) {
                    m_set_coeffs[i].push_back(f_pred.get_coeffs(i));
                }
                m_set_op.push_back(f_pred.get_op());
                m_set_const.push_back(f_pred.get_const());
            }
        }
    }

    expr_ref get_conj_coeffs(unsigned i, unsigned j) {
        return expr_ref(m_set_coeffs.get(i).get(j),m_conj_manager);
    }

    expr_ref get_conj_const(unsigned i) {
        return expr_ref(m_set_const.get(i), m_conj_manager);
    }

    unsigned get_ops(unsigned i) {
        return  m_set_op.get(i);
    }

    unsigned conj_size() {
        return m_set_op.size();
    }

    unsigned get_param_pred_count() {
        return m_param_pred_count;
    }

    void display() {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            std::cout << mk_pp(m_vars[i].get(), m_conj_manager) << "   ";
        }
        std::cout << "\n";
        for (unsigned i = 0; i < m_set_coeffs[0].size(); ++i) {
            for (unsigned j = 0; j < m_vars.size(); ++j) {
                std::cout << mk_pp(m_set_coeffs[j][i].get(), m_conj_manager) << "   ";
            }
            std::cout << m_set_op[i] << "   " << mk_pp(m_set_const[i].get(), m_conj_manager) << "\n";
        }
    }
};

class farkas_imp {
    expr_ref_vector m_vars;
    farkas_conj m_lhs;
    farkas_pred m_rhs;
    expr_ref_vector m_lambdas;
    expr_ref_vector m_solutions;
    expr_ref m_constraints;

    vector<lambda_kind> m_lambda_kinds;
    bool m_mk_lambda_kinds;

    ast_manager& m_imp_manager;

public:
    farkas_imp(expr_ref_vector vars, bool mk_lambda_kinds = false) : m_vars(vars), m_lhs(vars), m_rhs(vars),
        m_lambdas(vars.get_manager()), m_solutions(vars.get_manager()),
        m_constraints((vars.get_manager()).mk_true(), vars.get_manager()),
        m_mk_lambda_kinds(mk_lambda_kinds),
        m_imp_manager(vars.get_manager()) {
    }

    void set(expr_ref lhs_term, expr_ref rhs_term) {
        expr_ref_vector conjs(m_imp_manager);
        conjs.append(to_app(lhs_term)->get_num_args(), to_app(lhs_term)->get_args());
        for (unsigned i = 0; i < conjs.size(); ++i) {
            farkas_pred f_pred(m_vars);
            f_pred.put(expr_ref(conjs.get(i), m_imp_manager));
            m_lhs.add(f_pred);
        }
        m_rhs.put(rhs_term);
        set_constraint();
    }

    bool solve_constraint() {
        smt_params new_param;;
        smt::kernel solver(m_imp_manager, new_param);
        solver.assert_expr(m_constraints);
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            expr_ref solution(m_imp_manager);
            for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
                if (modref.get()->eval(m_lambdas.get(j), solution, true)) {
                    m_solutions.push_back(solution);
                }
                else {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    expr_ref_vector get_lambdas() {
        return m_lambdas;
    }

    expr_ref_vector get_solutions() {
        return m_solutions;
    }

    expr_ref get_constraints() {
        return m_constraints;
    }

    vector<lambda_kind> get_lambda_kinds() {
        return m_lambda_kinds;
    }

    void display() {
        ast_manager m = m_vars.get_manager();
        std::cout << "LHS: \n";
        m_lhs.display();
        std::cout << "RHS: \n";
        m_rhs.display();
        std::cout << "Constraint: \n" << mk_pp(m_constraints.get(), m) << "\n";
        if (m_solutions.size() > 0) {
            std::cout << "Solutions: \n";
        }
        for (unsigned i = 0; i < m_solutions.size(); ++i) {
            std::cout << mk_pp(m_lambdas[i].get(), m) << " --> " << mk_pp(m_solutions[i].get(), m) << "\n";
        }
    }

private:

    void set_constraint() {
        arith_util arith(m_imp_manager);
        SASSERT(m_lhs.get_param_pred_count() > 0);

        for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
            m_lambdas.push_back(expr_ref(m_imp_manager.mk_fresh_const("t", arith.mk_int()), m_imp_manager));
            if (m_lhs.get_ops(i) == 1) {
                m_constraints = m_imp_manager.mk_and(m_constraints, arith.mk_ge(m_lambdas.get(i), arith.mk_numeral(rational(0), true)));
            }
        }

        if (m_lhs.get_param_pred_count() == 1 && m_lhs.get_ops(0) != 0) {
            m_constraints = m_imp_manager.mk_and(m_constraints, m_imp_manager.mk_eq(m_lambdas.get(0), arith.mk_numeral(rational(1), true)));
        }

        if (m_mk_lambda_kinds) {
            set_lambda_kinds();
        }

        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref sum(arith.mk_numeral(rational(0), true), m_imp_manager);
            for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
                sum = arith.mk_add(sum, arith.mk_mul(m_lambdas.get(j), m_lhs.get_conj_coeffs(i, j)));
            }
            m_constraints = m_imp_manager.mk_and(m_constraints, m_imp_manager.mk_eq(sum, m_rhs.get_coeffs(i)));
        }

        expr_ref sum_const(arith.mk_numeral(rational(0), true), m_imp_manager);
        for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
            sum_const = arith.mk_add(sum_const, arith.mk_mul(m_lambdas.get(j), m_lhs.get_conj_const(j)));
        }
        m_constraints = m_imp_manager.mk_and(m_constraints, arith.mk_le(sum_const, m_rhs.get_const()));
    }

    void set_lambda_kinds() {
        arith_util arith(m_imp_manager);
        if (m_lhs.get_param_pred_count() == 1) {
            if (m_lhs.get_ops(0) == 0) {
                m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(0), m_imp_manager), bilin_sing, m_lhs.get_ops(0)));
            }
        }
        else {
            for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
                if (i < m_lhs.get_param_pred_count()) {
                    m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m_imp_manager), bilin, m_lhs.get_ops(i)));
                }
                else {
                    m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m_imp_manager), lin, m_lhs.get_ops(i)));
                }
            }
        }
    }
};

bool exists_valid(expr_ref& formula, expr_ref_vector& vars, app_ref_vector& q_vars, expr_ref& constraint_st);

bool well_founded(expr_ref_vector vars, expr_ref& LHS, expr_ref& bound, expr_ref& decrease);

void well_founded_cs(expr_ref_vector vsws, expr_ref& bound, expr_ref& decrease);

expr_ref_vector vars_difference(expr_ref_vector source, expr_ref_vector to_remove);

bool mk_exists_forall_farkas(expr_ref& fml, expr_ref_vector vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds);

void mk_bilin_lambda_constraint(vector<lambda_kind> lambda_kinds, int max_lambda, expr_ref& cons);

void mk_binder(expr_ref_vector vars, expr_ref_vector args, expr_ref& cs);

expr_ref_vector get_all_pred_vars(expr_ref& fml);

static bool replace_pred(expr_ref_vector args, expr_ref_vector vars, expr_ref& pred);

bool interpolate(expr_ref_vector vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol);

bool solve_clauses(core_clauses clauses, ast_manager& m, vector<refine_pred_info>& interpolants);

bool solve_clauses2(core_clauses clauses, ast_manager& m, vector<refine_pred_info>& interpolants);

void mk_conj(expr_ref_vector terms, expr_ref& conj);

void mk_conj(expr_ref term1, expr_ref term2, expr_ref& conj);

struct rel_template {
    app* m_head;
    expr_ref m_body;

    rel_template(app* head, expr_ref body) : m_head(head), m_body(body) {
    }
};

class rel_template_suit {

    ast_manager& m_rel_manager;

    vector<rel_template> m_rel_templates;
    vector<rel_template> m_rel_templates_orig;
    vector<rel_template> m_rel_template_instances;

    expr_ref_vector m_params;
    expr_ref m_extras;
    expr_ref m_extra_sol;
    expr_ref m_acc;

    vector<symbol> m_names;

    expr_ref subst_template_body(expr_ref fml, vector<rel_template> rel_templates);
    expr_ref subst_template_body(expr_ref fml, vector<rel_template> rel_templates, expr_ref_vector& args);

    var_subst m_var_subst;
    expr_ref_vector m_extra_subst;
    expr_ref_vector m_temp_subst;

    model_ref m_modref;

public:

    rel_template_suit(ast_manager& m) : m_rel_manager(m),
        m_extras(m_rel_manager),
        m_extra_sol(m_rel_manager),
        m_acc(expr_ref(m_rel_manager.mk_true(), m_rel_manager)),
        m_params(m_rel_manager),
        m_var_subst(m_rel_manager, false),
        m_extra_subst(m_rel_manager),
        m_temp_subst(m_rel_manager) {
    }

    void process_template_extra(expr_ref_vector& t_params, expr_ref extras) {
        m_params.append(t_params);
        m_extras = extras;
    }

    void process_template(symbol head_name, rel_template aa, expr_ref_vector temp_subst) {
        m_rel_templates.push_back(aa);
        m_names.push_back(head_name);
        m_temp_subst.append(temp_subst);
    }

    void process_template_sk(rel_template aa) {
        m_rel_templates_orig.push_back(aa);
    }

    void init_template_instantiate() {
        std::cout << "init_template_instantiate\n";
        if (m_rel_templates.size() == 0) {
            return;
        }
        display();
        std::cout << "m_extras  : " << mk_pp(m_extras, m_rel_manager) << "\n";
        smt_params new_param;
        smt::kernel solver(m_rel_manager, new_param);
        solver.assert_expr(m_extras);
        solver.display(std::cout);
        if (solver.check() == l_true) {
            solver.get_model(m_modref);
            for (unsigned i = 0; i < m_rel_templates.size(); i++) {
                expr_ref instance(m_rel_manager);
                if (m_modref.get()->eval(m_rel_templates[i].m_body, instance)) {
                    m_rel_template_instances.push_back(rel_template(m_rel_templates[i].m_head, instance));
                }
            }
        }
    }

    bool constrain_template(expr_ref fml) {
        if (m_rel_templates.size() == 0) {
            return false;
        }
        std::cout << "constrain_template begin ...\n";
        reset();
        display();
        if (!fml.m().is_true(fml)) {
            m_acc = fml.m().mk_and(fml, m_acc);
        }
        expr_ref_vector args_coll(m_rel_manager);
        expr_ref c1(subst_template_body(m_acc, m_rel_templates, args_coll), m_rel_manager);
        args_coll.append(m_temp_subst);

        expr_ref constraint_st(m_rel_manager.mk_true(), m_rel_manager);
        vector<lambda_kind> all_lambda_kinds;
        if (mk_exists_forall_farkas(c1, args_coll, constraint_st, true, all_lambda_kinds)) {
            expr_ref lambda_cs(m_rel_manager.mk_true(), m_rel_manager);
            int max_lambda = 2;
            mk_bilin_lambda_constraint(all_lambda_kinds, max_lambda, lambda_cs);

            smt_params new_param;
            smt::kernel solver(m_rel_manager, new_param);
            solver.assert_expr(constraint_st);
            solver.assert_expr(lambda_cs);
            solver.assert_expr(m_extras);
            if (solver.check() == l_true) {
                model_ref modref;
                solver.get_model(modref);
                for (unsigned i = 0; i < m_rel_templates.size(); i++) {
                    expr_ref instance(m_rel_manager);
                    if (modref.get()->eval(m_rel_templates[i].m_body, instance)) {
                        std::cout << "instance  : " << mk_pp(instance, m_rel_manager) << "\n";
                        m_rel_template_instances.push_back(rel_template(m_rel_templates[i].m_head, instance));

                    }
                    else {
                        // at least one template can't have a satisfying instance
                        return false;
                    }
                }
                // each template has a satisfying instance
                return true;
            }
        }
        return false;
    }

    vector<rel_template> get_template_instances() {
        return m_rel_template_instances;
    }

    vector<rel_template> get_templates() {
        return m_rel_templates;
    }

    bool get_orig_template(app* in_head, expr_ref& body) {
        for (unsigned i = 0; i < m_rel_templates.size(); i++) {
            if (m_rel_templates.get(i).m_head->get_decl()->get_name() == in_head->get_decl()->get_name()) {
                body = m_rel_templates_orig.get(i).m_body;
                return true;
            }
        }
        return false;
    }

    vector<rel_template> get_orig_templates() {
        return m_rel_templates_orig;
    }

    bool get_instance(app* head, expr_ref& body, expr_ref_vector& vars) {
        for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
            if (m_rel_template_instances[i].m_head->get_decl()->get_name() == head->get_decl()->get_name()) {
                body = m_rel_template_instances[i].m_body;
                vars.append(m_rel_template_instances[i].m_head->get_decl()->get_arity(), m_rel_template_instances[i].m_head->get_args());
                return true;
            }
        }
        return false;
    }

    unsigned get_params_count() {
        return m_params.size();
    }

    expr_ref_vector get_params() {
        return m_params;
    }

    void display() {
        std::cout << "templates: " << m_rel_templates.size() << "\n";
        for (unsigned i = 0; i < m_rel_templates.size(); i++) {
            std::cout << "template " << i << " : " << m_rel_templates[i].m_head->get_decl()->get_name() << " / " << m_rel_templates[i].m_head->get_decl()->get_arity() << "\n";
            std::cout << "template body : " << mk_pp(m_rel_templates[i].m_body, m_rel_manager) << "\n";
            std::cout << "template head : " << mk_pp(m_rel_templates[i].m_head, m_rel_manager) << "\n";
        }
        std::cout << "instances: " << m_rel_template_instances.size() << "\n";
        for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
            std::cout << "instance " << i << " : " << m_rel_template_instances[i].m_head->get_decl()->get_name() << " / " << m_rel_template_instances[i].m_head->get_decl()->get_arity() << "\n";
            std::cout << "instance body : " << mk_pp(m_rel_template_instances[i].m_body, m_rel_manager) << "\n";
            std::cout << "instance head : " << mk_pp(m_rel_template_instances[i].m_head, m_rel_manager) << "\n";

            expr_ref_vector inst_body_terms(m_rel_manager);
            get_conj_terms(m_rel_template_instances[i].m_body, inst_body_terms);
            std::cout << "inst_body_terms: " << inst_body_terms.size() << "\n";
            for (unsigned j = 0; j < inst_body_terms.size(); j++) {
                std::cout << "inst_body_terms : " << mk_pp(inst_body_terms.get(j), m_rel_manager) << "\n";
            }
        }

        std::cout << "orig templates: " << m_rel_templates_orig.size() << "\n";
        for (unsigned i = 0; i < m_rel_templates_orig.size(); i++) {
            std::cout << "orig template " << i << " : " << m_rel_templates_orig[i].m_head->get_decl()->get_name() << " / " << m_rel_templates_orig[i].m_head->get_decl()->get_arity() << "\n";
            std::cout << "orig template body : " << mk_pp(m_rel_templates_orig[i].m_body, m_rel_manager) << "\n";
            std::cout << "orig template head : " << mk_pp(m_rel_templates_orig[i].m_head, m_rel_manager) << "\n";
        }
    }

    expr_ref_vector get_temp_subst() {
        return m_temp_subst;
    }

    vector<symbol> get_names() {
        return  m_names;
    }

    ast_manager& get_rel_manager() {
        return m_rel_manager;
    }

    expr_ref get_extras() {
        return m_extras;
    }

    model_ref get_modref() {
        return m_modref;
    }

    void reset() {
        m_rel_template_instances.reset();
    }
};
