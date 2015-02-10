/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    farkas_util.cpp

Abstract:

    Utilities for applying farkas lemma over linear implications.

Author:

    Tewodros A. Beyene (t-tewbe) 2014-10-22.

Revision History:

--*/
#include "predabst_util.h"
#include "farkas_util.h"
#include "th_rewriter.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "ast_pp.h"
#include "smt_kernel.h"
#include "smt_params.h"
#include "qe_lite.h"

typedef enum { bilin_sing, bilin, lin } lambda_kind_sort;

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

static bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds);
static expr_ref mk_bilin_lambda_constraint(vector<lambda_kind> const& lambda_kinds, int max_lambda, ast_manager& m);
static bool interpolate(expr_ref_vector const& vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol);

template<class T>
static void push_front(vector<T>& v, T e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

template<class T, class TManager>
static void push_front(ref_vector<T, TManager>& v, obj_ref<T, TManager> e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

static expr_ref_vector get_all_terms(expr_ref const& term) {
    expr_ref_vector all_facts(term.m());
    if (!arith_util(term.m()).is_mul(term)) {
        all_facts.push_back(term);
    }
    else {
        expr_ref_vector facts(term.m());
        facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        for (unsigned i = 0; i < facts.size(); ++i) {
            all_facts.append(get_all_terms(expr_ref(facts.get(i), term.m())));
        }
    }
    return all_facts;
}

static void get_all_terms(expr_ref const& term, expr_ref_vector const& vars, expr_ref_vector& var_facts, expr_ref_vector& const_facts, bool& has_params) {
    if (!arith_util(term.m()).is_mul(term)) {
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
            get_all_terms(expr_ref(facts.get(i), term.m()), vars, var_facts, const_facts, has_params);
        }
    }
}

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

    void display(std::ostream& out) const {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (i == 0) {
                out << mk_pp(m_coeffs[i], m_pred_manager) << " * " << mk_pp(m_vars[i], m_pred_manager);
            }
            else {
                out << " + " << mk_pp(m_coeffs[i], m_pred_manager) << " * " << mk_pp(m_vars[i], m_pred_manager);
            }
        }
        switch (m_op) {
        case 0:
            out << " = ";
            break;
        case 1:
            out << " =< ";
            break;
        case 2:
            out << " >= ";
            break;
        case 3:
            out << " < ";
            break;
        case 4:
            out << " > ";
            break;
        default:
            out << " Unknown relation! ";
            break;
        }
        out << mk_pp(m_const, m_pred_manager) << "\n";
        out << "Params? : " << (m_has_params ? "TRUE" : "FALSE") << "\n";
    }

private:

    void rewrite_pred(expr_ref& term) {
        arith_util arith(term.m());
        expr *e1;
        expr *e2;
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
            STRACE("predabst", tout << "Unable to recognize predicate " << mk_pp(term, term.m()) << "\n";);
            UNREACHABLE();
        }
        th_rewriter rw(term.m());
        rw(term);
    }

    void set(expr_ref& term) {
        arith_util arith(m_pred_manager);
        rewrite_pred(term);
        expr_ref_vector p_coeffs(m_pred_manager), p_vars(m_pred_manager), p_const_facts(m_pred_manager), add_facts(m_pred_manager);
        if (arith.is_add(term)) {
            add_facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        }
        else {
            add_facts.push_back(term);
        }
        for (unsigned i = 0; i < add_facts.size(); ++i) {
            expr_ref_vector mul_facts(m_pred_manager), var_mul_facts(m_pred_manager), const_mul_facts(m_pred_manager);
            expr_ref mul_term(add_facts.get(i), m_pred_manager);
            get_all_terms(mul_term, m_vars, var_mul_facts, const_mul_facts, m_has_params);
            CASSERT("predabst", var_mul_facts.size() <= 1);
            if (var_mul_facts.size() == 0) {
                p_const_facts.push_back(add_facts.get(i));
            }
            else if (const_mul_facts.size() == 0) {
                p_vars.push_back(add_facts.get(i));
                p_coeffs.push_back(arith.mk_numeral(rational(1), true));
            }
            else if (const_mul_facts.size() == 1) {
                p_vars.push_back(var_mul_facts.get(0));
                p_coeffs.push_back(const_mul_facts.get(0));
            }
            else {
                p_vars.push_back(var_mul_facts.get(0));
                p_coeffs.push_back(arith.mk_mul(const_mul_facts.size(), const_mul_facts.c_ptr()));
            }
        }
        if (p_const_facts.size() == 0) {
            m_const = arith.mk_numeral(rational(0), true);
        }
        else if (p_const_facts.size() == 1) {
            m_const = arith.mk_uminus(p_const_facts.get(0));
        }
        else {
            m_const = arith.mk_uminus(arith.mk_add(p_const_facts.size(), p_const_facts.c_ptr()));
        }
        th_rewriter rw(m_pred_manager);
        rw(m_const);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            for (unsigned j = 0; j < p_vars.size(); ++j) {
                if (m_vars.get(i) == p_vars.get(j)) {
                    m_coeffs.set(i, p_coeffs.get(j));
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
    mutable ast_manager m_conj_manager;


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
                    push_front(m_set_coeffs[i], f_pred.get_coeffs(i));
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
        return expr_ref(m_set_coeffs.get(i).get(j), m_conj_manager);
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

    void display(std::ostream& out) const {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            out << mk_pp(m_vars[i], m_conj_manager) << "   ";
        }
        out << "\n";
        for (unsigned i = 0; i < m_set_coeffs[0].size(); ++i) {
            for (unsigned j = 0; j < m_vars.size(); ++j) {
                out << mk_pp(m_set_coeffs[j][i], m_conj_manager) << "   ";
            }
            out << m_set_op[i] << "   " << mk_pp(m_set_const[i], m_conj_manager) << "\n";
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
                if (modref->eval(m_lambdas.get(j), solution, true)) {
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

    void display(std::ostream& out) const {
        ast_manager m = m_vars.get_manager();
        out << "LHS: \n";
        m_lhs.display(out);
        out << "RHS: \n";
        m_rhs.display(out);
        out << "Constraint: \n" << mk_pp(m_constraints, m) << "\n";
        if (m_solutions.size() > 0) {
            out << "Solutions: \n";
        }
        for (unsigned i = 0; i < m_solutions.size(); ++i) {
            out << mk_pp(m_lambdas[i], m) << " --> " << mk_pp(m_solutions[i], m) << "\n";
        }
    }

private:

    void set_constraint() {
        arith_util arith(m_imp_manager);
        CASSERT("predabst", m_lhs.get_param_pred_count() > 0);

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

static bool exists_valid(expr_ref const& fml, expr_ref_vector const& vars, app_ref_vector const& q_vars, expr_ref& constraint_st) {
    ast_manager& m = fml.m();
    constraint_st = m.mk_true();
    expr_ref norm_fml = neg_and_2dnf(fml);
    CASSERT("predabst", fml.m().is_or(norm_fml));
    for (unsigned i = 0; i < to_app(norm_fml)->get_num_args(); ++i) {
        expr_ref disj(to_app(norm_fml)->get_arg(i), fml.m());
        app_ref_vector q_vars_disj(q_vars);
        qe_lite ql1(fml.m());
        ql1(q_vars_disj, disj);
        farkas_imp f_imp(vars);
        f_imp.set(disj, expr_ref(m.mk_false(), m));
        if (!f_imp.solve_constraint()) {
            return false;
        }
        constraint_st = m.mk_and(constraint_st, f_imp.get_constraints());
    }
    return true;
}

static bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds) {
    expr_ref norm_fml = neg_and_2dnf(fml);
    CASSERT("predabst", fml.m().is_or(norm_fml));
    expr_ref_vector disjs(fml.m());
    disjs.append(to_app(norm_fml)->get_num_args(), to_app(norm_fml)->get_args());
    for (unsigned i = 0; i < disjs.size(); ++i) {
        farkas_imp f_imp(vars, mk_lambda_kinds);
        f_imp.set(expr_ref(disjs.get(i), fml.m()), expr_ref(fml.m().mk_false(), fml.m()));
        if (f_imp.solve_constraint()) {
            constraint_st = fml.m().mk_and(constraint_st, f_imp.get_constraints());
            all_lambda_kinds.append(f_imp.get_lambda_kinds());
        }
        else {
            return false;
        }
    }
    return true;
}

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref sol_bound, expr_ref sol_decrease) {
    ast_manager& m = lhs.get_manager();
    if (m.is_true(lhs) || !m.is_and(lhs) || to_app(lhs)->get_num_args() <= 1 || (vsws.size() % 2) != 0) {
        return false;
    }

    expr_ref_vector lhs_vars(get_all_vars(lhs));

    expr_ref_vector vs(m);
    bool hasv = false;
    for (unsigned i = 0; i < (vsws.size() / 2); i++) {
        vs.push_back(vsws.get(i));
        hasv = hasv || lhs_vars.contains(vsws.get(i));
    }
    if (!hasv) {
        return false;
    }

    expr_ref_vector ws(m);
    bool hasw = false;
    for (unsigned i = (vsws.size() / 2); i < vsws.size(); ++i) {
        ws.push_back(vsws.get(i));
        hasw = hasw || lhs_vars.contains(vsws.get(i));
    }
    if (!hasw) {
        return false;
    }

    app_ref_vector q_vars(m);
    for (unsigned j = 0; j < lhs_vars.size(); j++) {
        if (!vsws.contains(lhs_vars.get(j))) {
            q_vars.push_back(to_app(lhs_vars.get(j)));
        }
    }

    arith_util arith(m);
    expr_ref_vector params(m);
    expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
    expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        params.push_back(param);
        sum_psvs = arith.mk_add(sum_psvs, arith.mk_mul(param, vs.get(i)));
        sum_psws = arith.mk_add(sum_psws, arith.mk_mul(param, ws.get(i)));
    }

    expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);
    params.push_back(delta0);

    expr_ref bound(arith.mk_ge(sum_psvs, delta0), m);
    expr_ref decrease(arith.mk_lt(sum_psws, sum_psvs), m);
    expr_ref to_solve(m.mk_or(m.mk_not(lhs), m.mk_and(bound, decrease)), m);

    STRACE("predabst", tout << "bound: " << mk_pp(bound, m) << "\n";);
    STRACE("predabst", tout << "decrease: " << mk_pp(decrease, m) << "\n";);
    expr_ref constraint_st(m);
    if (exists_valid(to_solve, vsws, q_vars, constraint_st)) {
        smt_params new_param;
        smt::kernel solver(m, new_param);
        solver.assert_expr(constraint_st);
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            if (modref->eval(bound, sol_bound) && modref->eval(decrease, sol_decrease)) {
                return true;
            }
            return false; // when does it happen?
        }
        return false; //unsat param
    }
    return false; //unsat lambda
}

void well_founded_cs(expr_ref_vector const& vsws, expr_ref bound, expr_ref decrease) {
    ast_manager& m = vsws.get_manager();
    arith_util arith(m);

    expr_ref_vector vs(m);
    expr_ref_vector ws(m);
    for (unsigned i = 0; i < vsws.size(); i++) {
        if (i < (vsws.size() / 2)) {
            vs.push_back(vsws.get(i));
        }
        else {
            ws.push_back(vsws.get(i));
        }
    }
    expr_ref_vector params(m);
    expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
    expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        params.push_back(param);
        sum_psvs = arith.mk_add(sum_psvs, arith.mk_mul(param, vs.get(i)));
        sum_psws = arith.mk_add(sum_psws, arith.mk_mul(param, ws.get(i)));
    }

    expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);
    params.push_back(delta0);

    bound = arith.mk_ge(sum_psvs, delta0);
    decrease = arith.mk_lt(sum_psws, sum_psvs);

    STRACE("predabst", tout << "bound: " << mk_pp(bound, m) << "\n";);
    STRACE("predabst", tout << "decrease: " << mk_pp(decrease, m) << "\n";);
}

static expr_ref mk_bilin_lambda_constraint(vector<lambda_kind> const& lambda_kinds, int max_lambda, ast_manager& m) {
    arith_util arith(m);

    expr_ref n1(arith.mk_numeral(rational(1), true), m);
    expr_ref nminus1(arith.mk_numeral(rational(-1), true), m);

    int min_lambda = -1 * max_lambda;

    expr_ref cons(m.mk_true(), m);
    for (unsigned i = 0; i < lambda_kinds.size(); i++) {
        if (lambda_kinds[i].m_kind == bilin_sing) {
            cons = m.mk_and(cons, m.mk_or(m.mk_eq(lambda_kinds[i].m_lambda, nminus1), m.mk_eq(lambda_kinds[i].m_lambda, n1)));
        }
        else if (lambda_kinds[i].m_kind == bilin) {
            if (lambda_kinds[i].m_op != 0) {
                min_lambda = 0; // operator not equality
            }
            expr_ref bilin_disj(m.mk_true(), m);
            for (int j = min_lambda; j <= max_lambda; j++) {
                bilin_disj = m.mk_or(bilin_disj, m.mk_eq(lambda_kinds[i].m_lambda, arith.mk_numeral(rational(j), true)));
            }
            cons = m.mk_and(cons, bilin_disj);
        }
    }
    return cons;
}

static void display_core_clauses(std::ostream& out, ast_manager& m, core_clauses const& clauses) {
    core_clauses::const_iterator st = clauses.begin();
    core_clauses::const_iterator end = clauses.end();
    for (; st != end; st++) {
        out << "clause --> " << st->first << " [";
        for (unsigned i = 0; i < st->second.first.size(); i++) {
            out << mk_pp(st->second.first.get(i), m) << " ";
        }
        out << "] : " << mk_pp(st->second.second.first, m) << " [";
        for (unsigned i = 0; i < st->second.second.second.size(); i++) {
            out << mk_pp(st->second.second.second.get(i), m) << " ";
        }
        out << "]\n";
    }
}

static void display_core_clauses2(std::ostream& out, ast_manager& m, core_clauses2 const& clauses) {
    for (unsigned j = 0; j < clauses.size(); j++) {
        out << "clause --> " << clauses.get(j).first->get_name() << " [";
        for (unsigned i = 0; i < clauses.get(j).second.first.size(); i++) {
            out << mk_pp(clauses.get(j).second.first.get(i), m) << " ";
        }
        out << "] : " << mk_pp(clauses.get(j).second.second.first, m) << " [";
        for (unsigned i = 0; i < clauses.get(j).second.second.second.size(); i++) {
            out << mk_pp(clauses.get(j).second.second.second.get(i), m) << " ";
        }
        out << "]\n";
    }
}

// XXX use print_expr_ref_vector instead
static void display_expr_ref_vector(std::ostream& out, expr_ref_vector const& vect) {
    out << "expr vect --> [";
    for (unsigned i = 0; i < vect.size(); i++) {
        out << mk_pp(vect.get(i), vect.m()) << " ";
    }
    out << "]\n";
}

expr_ref rel_template_suit::subst_template_body(expr_ref const& fml, vector<rel_template> const& rel_templates, expr_ref_vector& args_coll) {
    ast_manager& m = fml.get_manager();
    expr_ref new_formula(m);
    expr_ref_vector sub_formulas(m);
    expr_ref_vector new_sub_formulas(m);
    if (m.is_and(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas.get(i), m), rel_templates, args_coll));
        }
        new_formula = m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr());
    }
    else if (m.is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas.get(i), m), rel_templates, args_coll));
        }
        new_formula = m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr());

    }
    else if (m.is_not(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        new_formula = m.mk_not(subst_template_body(expr_ref(sub_formulas.get(0), m), rel_templates, args_coll));
    }
    else {
        if (m_names.contains(to_app(fml)->get_decl())) {
            for (unsigned i = 0; i < rel_templates.size(); i++) {
                if (to_app(fml)->get_decl() == rel_templates.get(i).m_head->get_decl()) {
                    expr_ref cs(m_rel_templates_orig.get(i).m_body);
                    expr_ref_vector args(m, to_app(fml)->get_decl()->get_arity(), to_app(fml)->get_args());
                    args_coll.append(args);
                    args.append(m_params);
                    args.reverse();
                    m_var_subst(cs, args.size(), args.c_ptr(), cs);
                    return cs;
                }
            }
        }
        return fml;
    }
    return new_formula;
}

static void interpolate_helper(expr_ref_vector const& vars, expr_ref &fml) {
    ast_manager& m = fml.get_manager();
    qe_lite ql(m);
    app_ref_vector q_vars(m);
    expr_ref_vector all_vars = get_all_vars(fml);
    for (unsigned j = 0; j < all_vars.size(); j++) {
        if (!vars.contains(all_vars.get(j))) {
            q_vars.push_back(to_app(all_vars.get(j)));
        }
    }
    ql(q_vars, fml);
}

static bool interpolate(expr_ref_vector const& vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol) {
    interpolate_helper(vars, fmlA);
    interpolate_helper(vars, fmlB);

    ast_manager& m = vars.get_manager();
    arith_util arith(m);
    expr_ref_vector params(m);
    expr_ref sum_vars(arith.mk_numeral(rational(0), true), m);
    for (unsigned i = 0; i < vars.size(); ++i) {
        expr_ref param(m.mk_fresh_const("i", arith.mk_int()), m);
        params.push_back(param);
        sum_vars = arith.mk_add(sum_vars, arith.mk_mul(param, vars.get(i)));
    }
    expr_ref ic(m.mk_const(symbol("ic"), arith.mk_int()), m);
    params.push_back(ic);
    expr_ref fmlQ(arith.mk_le(sum_vars, ic), m);

    expr_ref to_solve(m.mk_and(m.mk_or(m.mk_not(fmlA), fmlQ), m.mk_or(m.mk_not(fmlQ), m.mk_not(fmlB))), m);

    app_ref_vector q_vars(m);
    expr_ref constraint_st(m);
    if (exists_valid(to_solve, vars, q_vars, constraint_st)) {
        smt_params new_param;
        smt::kernel solver(m, new_param);
        solver.assert_expr(constraint_st);
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            if (modref->eval(fmlQ, fmlQ_sol)) {
                return true;
            }
            // when does it happen?
        }
    }
    return false;
}

vector<refine_pred_info> solve_clauses(core_clauses const& clauses, ast_manager& m) {
    vector<refine_pred_info> interpolants;
        
    core_clauses::const_iterator end = clauses.end();
    end--;
    for (int i = clauses.size() - 1; i >= 1; i--) {
        int j = clauses.size() - 1;
        core_clauses::const_iterator end2 = end;

        expr_ref fmlA(m.mk_true(), m);
        for (; j >= i; j--, end2--) {
            fmlA = mk_conj(fmlA, end2->second.second.first);
        }

        core_clauses::const_iterator end4 = end2;
        end4++;
        expr_ref_vector vars(end4->second.first);

        expr_ref fmlB(m.mk_true(), m);
        for (; j >= 0; j--, end2--) {
            fmlB = mk_conj(fmlB, end2->second.second.first);
        }

        expr_ref fmlQ_sol(m);
        if (interpolate(vars, fmlA, fmlB, fmlQ_sol)) {
            interpolants.push_back(refine_pred_info(fmlQ_sol, get_all_vars(fmlQ_sol)));
        }
    }

    return interpolants;
}

static void print_node_info(std::ostream& out, unsigned added_id, func_decl* sym, vector<bool> const& cube, unsigned r_id, vector<unsigned> const& parent_nodes) {
    out << "Node added: (" << added_id << ", " << sym->get_name().str() << ", " << r_id << ", [";
    for (unsigned i = 0; i < parent_nodes.size(); i++) {
        out << parent_nodes.get(i) << " ";
    }
    out << "]) " << ", [";
    for (unsigned i = 0; i < cube.size(); i++) {
        out << cube.get(i) << " ";
    }
    out << "]) \n";
}

void rel_template_suit::init_template_instantiate() {
    STRACE("predabst", tout << "init_template_instantiate\n"; display(tout););
    smt_params new_param;
    smt::kernel solver(m_rel_manager, new_param);
    if (m_extras) {
        solver.assert_expr(m_extras);
    }
    STRACE("predabst", solver.display(tout););
    if (solver.check() == l_true) {
        solver.get_model(m_modref);
        for (unsigned i = 0; i < m_rel_templates.size(); i++) {
            expr_ref instance(m_rel_manager);
            if (m_modref->eval(m_rel_templates[i].m_body, instance)) {
                m_rel_template_instances.push_back(rel_template(m_rel_templates[i].m_head, instance));
            }
        }
    }
}

bool rel_template_suit::get_orig_template(func_decl* fdecl, expr_ref& body) {
    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        rel_template const& orig = m_rel_templates_orig[i];
        if (orig.m_head->get_decl() == fdecl) {
            body = orig.m_body;
            return true;
        }
    }
    return false;
}

bool rel_template_suit::get_instance(func_decl* fdecl, expr_ref& body, expr_ref_vector& vars) {
    for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
        rel_template const& instance = m_rel_template_instances[i];
        if (instance.m_head->get_decl() == fdecl) {
            body = instance.m_body;
            vars.append(instance.m_head->get_num_args(), instance.m_head->get_args());
            return true;
        }
    }
    return false;
}

bool rel_template_suit::constrain_template(expr_ref const& fml) {
    if (m_rel_templates.size() == 0) { // XXX remove this check eventually
        return false;
    }
    reset();
    STRACE("predabst", tout << "constrain_template begin\n"; display(tout););
    if (!fml.m().is_true(fml)) {
        m_acc = fml.m().mk_and(fml, m_acc);
    }
    expr_ref_vector args_coll(m_rel_manager);
    expr_ref c1(subst_template_body(m_acc, m_rel_templates, args_coll), m_rel_manager);
    //args_coll.append(m_temp_subst); //>>> I have no idea what this was trying to do, but m_temp_subst is no more

    expr_ref constraint_st(m_rel_manager.mk_true(), m_rel_manager);
    vector<lambda_kind> all_lambda_kinds;
    if (mk_exists_forall_farkas(c1, args_coll, constraint_st, true, all_lambda_kinds)) {
        int max_lambda = 2;
        expr_ref lambda_cs = mk_bilin_lambda_constraint(all_lambda_kinds, max_lambda, m_rel_manager);

        smt_params new_param;
        smt::kernel solver(m_rel_manager, new_param);
        solver.assert_expr(constraint_st);
        solver.assert_expr(lambda_cs);
        if (m_extras) {
            solver.assert_expr(m_extras);
        }
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            for (unsigned i = 0; i < m_rel_templates.size(); i++) {
                expr_ref instance(m_rel_manager);
                if (modref->eval(m_rel_templates[i].m_body, instance)) {
                    STRACE("predabst", tout << "instance  : " << mk_pp(instance, m_rel_manager) << "\n";);
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

void rel_template_suit::display(std::ostream& out) const {
    out << "templates: " << m_rel_templates.size() << "\n";
    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        out << "template " << i << " : " << m_rel_templates[i].m_head->get_decl()->get_name() << " / " << m_rel_templates[i].m_head->get_decl()->get_arity() << "\n";
        out << "template body : " << mk_pp(m_rel_templates[i].m_body, m_rel_manager) << "\n";
        out << "template head : " << mk_pp(m_rel_templates[i].m_head, m_rel_manager) << "\n";
    }
    out << "instances: " << m_rel_template_instances.size() << "\n";
    for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
        out << "instance " << i << " : " << m_rel_template_instances[i].m_head->get_decl()->get_name() << " / " << m_rel_template_instances[i].m_head->get_decl()->get_arity() << "\n";
        out << "instance body : " << mk_pp(m_rel_template_instances[i].m_body, m_rel_manager) << "\n";
        out << "instance head : " << mk_pp(m_rel_template_instances[i].m_head, m_rel_manager) << "\n";

        expr_ref_vector inst_body_terms = get_conj_terms(m_rel_template_instances[i].m_body);
        out << "inst_body_terms: " << inst_body_terms.size() << "\n";
        for (unsigned j = 0; j < inst_body_terms.size(); j++) {
            out << "inst_body_terms : " << mk_pp(inst_body_terms.get(j), m_rel_manager) << "\n";
        }
    }

    out << "orig templates: " << m_rel_templates_orig.size() << "\n";
    for (unsigned i = 0; i < m_rel_templates_orig.size(); i++) {
        out << "orig template " << i << " : " << m_rel_templates_orig[i].m_head->get_decl()->get_name() << " / " << m_rel_templates_orig[i].m_head->get_decl()->get_arity() << "\n";
        out << "orig template body : " << mk_pp(m_rel_templates_orig[i].m_body, m_rel_manager) << "\n";
        out << "orig template head : " << mk_pp(m_rel_templates_orig[i].m_head, m_rel_manager) << "\n";
    }
}

void refine_pred_info::display(std::ostream& out) const {
    out << "pred: " << mk_pp(m_pred, m_pred.m()) << ", pred_vars: [";
    for (unsigned i = 0; i < m_pred_vars.size(); i++) {
        out << " " << mk_pp(m_pred_vars.get(i), m_pred.m());
    }
    out << "]\n";
}
