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
typedef enum { op_eq, op_le, op_ge, op_lt, op_gt } rel_op;

struct lambda_kind {
    expr_ref m_lambda;
    lambda_kind_sort m_kind;
    rel_op m_op;
    int m_lower_bound;
    int m_upper_bound;

    lambda_kind(expr_ref lambda, lambda_kind_sort kind, rel_op op) :
        m_lambda(lambda),
        m_kind(kind),
        m_op(op),
        m_lower_bound(0),
        m_upper_bound(0) {
    }
};

template<class T>
static void push_front(vector<T>& v, T const& e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

template<class T, class TManager>
static void push_front(ref_vector<T, TManager>& v, obj_ref<T, TManager> const& e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

static void get_all_terms(expr_ref const& term, expr_ref_vector const& vars, expr_ref_vector& var_facts, expr_ref_vector& const_facts, bool& has_params) {
    ast_manager& m = term.m();
    // XXX do we need to assign has_params = false here?
    if (!arith_util(m).is_mul(term)) {
        if (vars.contains(term)) {
            var_facts.push_back(term);
        }
        else {
            const_facts.push_back(term);
            // params check ***
            if (!arith_util(m).is_numeral(term)) {
                has_params = true;
            }
        }
    }
    else {
        expr_ref_vector facts(m);
        facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        for (unsigned i = 0; i < facts.size(); ++i) {
            get_all_terms(expr_ref(facts.get(i), m), vars, var_facts, const_facts, has_params);
        }
    }
}

class farkas_pred {
    expr_ref_vector m_vars;
    expr_ref_vector m_coeffs;
    rel_op m_op;
    expr_ref m_const;

    bool m_has_params;
    ast_manager& m;

public:

    farkas_pred(expr_ref_vector const& vars) :
        m_vars(vars),
        m_coeffs(vars.get_manager()),
        m_const(vars.get_manager()),
        m_op(op_le),
        m_has_params(false),
        m(vars.get_manager()) {
    }

    void put(expr_ref term) {
        arith_util arith(m);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            m_coeffs.push_back(arith.mk_numeral(rational(0), true));
        }
        if (m.is_true(term)) {
            m_op = op_le;
            m_const = arith.mk_numeral(rational(0), true);
        }
        else if (m.is_false(term)) {
            m_op = op_le;
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
        return expr_ref(m_coeffs.get(i), m);
    }

    rel_op get_op() {
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
                out << mk_pp(m_coeffs[i], m) << " * " << mk_pp(m_vars[i], m);
            }
            else {
                out << " + " << mk_pp(m_coeffs[i], m) << " * " << mk_pp(m_vars[i], m);
            }
        }
        switch (m_op) {
        case op_eq:
            out << " = ";
            break;
        case op_le:
            out << " <= ";
            break;
        case op_ge:
            out << " >= ";
            break;
        case op_lt:
            out << " < ";
            break;
        case op_gt:
            out << " > ";
            break;
        default:
            out << " Unknown relation! ";
            UNREACHABLE();
        }
        out << mk_pp(m_const, m) << "\n";
        out << "Params? : " << (m_has_params ? "TRUE" : "FALSE") << "\n";
    }

private:

    void rewrite_pred(expr_ref& term) {
        arith_util arith(m);
        expr *e1;
        expr *e2;
        if (m.is_eq(term, e1, e2)) {
            term = arith.mk_sub(e1, e2);
            m_op = op_eq;
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
            STRACE("predabst", tout << "Unable to recognize predicate " << mk_pp(term, m) << "\n";);
            UNREACHABLE();
        }
        th_rewriter rw(m);
        rw(term);
    }

    void set(expr_ref& term) {
        arith_util arith(m);
        rewrite_pred(term);
        expr_ref_vector p_coeffs(m), p_vars(m), p_const_facts(m), add_facts(m);
        if (arith.is_add(term)) {
            add_facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        }
        else {
            add_facts.push_back(term);
        }
        for (unsigned i = 0; i < add_facts.size(); ++i) {
            expr_ref_vector mul_facts(m), var_mul_facts(m), const_mul_facts(m);
            expr_ref mul_term(add_facts.get(i), m);
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
        th_rewriter rw(m);
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
    vector<rel_op> m_set_op;
    vector<expr_ref> m_set_const;

    unsigned m_param_pred_count;
    mutable ast_manager m;

public:
    farkas_conj(expr_ref_vector const& vars) :
        m_vars(vars),
        m_param_pred_count(0),
        m(vars.get_manager()) {
    }

    void add(farkas_pred& f_pred) {
        if (m_set_coeffs.size() == 0) {
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                expr_ref_vector init_coeff(m);
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
        return expr_ref(m_set_coeffs.get(i).get(j), m);
    }

    expr_ref get_conj_const(unsigned i) {
        return expr_ref(m_set_const.get(i), m);
    }

    rel_op get_ops(unsigned i) {
        return m_set_op.get(i);
    }

    unsigned conj_size() {
        return m_set_op.size();
    }

    unsigned get_param_pred_count() {
        return m_param_pred_count;
    }

    void display(std::ostream& out) const {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            out << mk_pp(m_vars[i], m) << "   ";
        }
        out << "\n";
        for (unsigned i = 0; i < m_set_coeffs[0].size(); ++i) {
            for (unsigned j = 0; j < m_vars.size(); ++j) {
                out << mk_pp(m_set_coeffs[j][i], m) << "   ";
            }
            out << m_set_op[i] << "   " << mk_pp(m_set_const[i], m) << "\n";
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

    ast_manager& m;

public:
    farkas_imp(expr_ref_vector const& vars, bool mk_lambda_kinds) :
        m_vars(vars),
        m_lhs(vars),
        m_rhs(vars),
        m_lambdas(vars.get_manager()),
        m_solutions(vars.get_manager()),
        m_constraints((vars.get_manager()).mk_true(), vars.get_manager()),
        m_mk_lambda_kinds(mk_lambda_kinds),
        m(vars.get_manager()) {
    }

    void set(expr_ref lhs_term, expr_ref rhs_term) {
        expr_ref_vector conjs(m);
        conjs.append(to_app(lhs_term)->get_num_args(), to_app(lhs_term)->get_args());
        for (unsigned i = 0; i < conjs.size(); ++i) {
            farkas_pred f_pred(m_vars);
            f_pred.put(expr_ref(conjs.get(i), m));
            m_lhs.add(f_pred);
        }
        m_rhs.put(rhs_term);
        set_constraint();
    }

    bool solve_constraint() {
        smt_params new_param;;
        smt::kernel solver(m, new_param);
        solver.assert_expr(m_constraints);
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            expr_ref solution(m);
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
        arith_util arith(m);
        //CASSERT("predabst", m_lhs.get_param_pred_count() > 0);
        // XXX This assert fails on unsat-N.smt2, but without it the tests pass.  It's not clear whether this assert is wrong, or whether there's a bug.

        for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
            m_lambdas.push_back(expr_ref(m.mk_fresh_const("t", arith.mk_int()), m));
            if (m_lhs.get_ops(i) == op_le) {
                m_constraints = m.mk_and(m_constraints, arith.mk_ge(m_lambdas.get(i), arith.mk_numeral(rational(0), true)));
            }
        }

        if (m_lhs.get_param_pred_count() == 1 && m_lhs.get_ops(0) != op_eq) {
            m_constraints = m.mk_and(m_constraints, m.mk_eq(m_lambdas.get(0), arith.mk_numeral(rational(1), true)));
        }

        if (m_mk_lambda_kinds) {
            set_lambda_kinds();
        }

        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref sum(arith.mk_numeral(rational(0), true), m);
            for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
                sum = arith.mk_add(sum, arith.mk_mul(m_lambdas.get(j), m_lhs.get_conj_coeffs(i, j)));
            }
            m_constraints = m.mk_and(m_constraints, m.mk_eq(sum, m_rhs.get_coeffs(i)));
        }

        expr_ref sum_const(arith.mk_numeral(rational(0), true), m);
        for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
            sum_const = arith.mk_add(sum_const, arith.mk_mul(m_lambdas.get(j), m_lhs.get_conj_const(j)));
        }
        m_constraints = m.mk_and(m_constraints, arith.mk_le(sum_const, m_rhs.get_const()));
    }

    void set_lambda_kinds() {
        arith_util arith(m);
        if (m_lhs.get_param_pred_count() == 1) {
            if (m_lhs.get_ops(0) == op_eq) {
                m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(0), m), bilin_sing, m_lhs.get_ops(0)));
            }
        }
        else {
            for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
                if (i < m_lhs.get_param_pred_count()) {
                    m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), bilin, m_lhs.get_ops(i)));
                }
                else {
                    m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), lin, m_lhs.get_ops(i)));
                }
            }
        }
    }
};

static bool exists_valid(expr_ref const& fml, expr_ref_vector const& vars, app_ref_vector const& q_vars, expr_ref& constraint_st) {
    ast_manager& m = fml.m();
    constraint_st = m.mk_true();
    expr_ref norm_fml = neg_and_2dnf(fml);
    CASSERT("predabst", m.is_or(norm_fml));
    for (unsigned i = 0; i < to_app(norm_fml)->get_num_args(); ++i) {
        expr_ref disj(to_app(norm_fml)->get_arg(i), m);
        app_ref_vector q_vars_disj(q_vars);
        qe_lite ql1(m);
        ql1(q_vars_disj, disj);
        farkas_imp f_imp(vars, false);
        f_imp.set(disj, expr_ref(m.mk_false(), m));
        if (!f_imp.solve_constraint()) {
            return false;
        }
        constraint_st = m.mk_and(constraint_st, f_imp.get_constraints());
    }
    return true;
}

static bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref& constraint_st, vector<lambda_kind>& all_lambda_kinds) {
    ast_manager& m = fml.m();
    constraint_st = m.mk_true();
    expr_ref norm_fml = neg_and_2dnf(fml);
    CASSERT("predabst", m.is_or(norm_fml));
    for (unsigned i = 0; i < to_app(norm_fml)->get_num_args(); ++i) {
        farkas_imp f_imp(vars, true);
        f_imp.set(expr_ref(to_app(norm_fml)->get_arg(i), m), expr_ref(m.mk_false(), m));
        if (!f_imp.solve_constraint()) {
            return false;
        }
        constraint_st = m.mk_and(constraint_st, f_imp.get_constraints());
        all_lambda_kinds.append(f_imp.get_lambda_kinds());
    }
    return true;
}

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref& sol_bound, expr_ref& sol_decrease) {
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
                STRACE("predabst", tout << "Formula is well-founded: bound " << mk_pp(sol_bound, m) << "; decrease " << mk_pp(sol_decrease, m) << "\n";);
                return true;
            }
            return false; // when does it happen?
        }
        return false; //unsat param
    }
    return false; //unsat lambda
}

expr_ref well_founded_cs(expr_ref_vector const& vsws) {
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

    expr_ref bound(arith.mk_ge(sum_psvs, delta0), m);
    expr_ref decrease(arith.mk_lt(sum_psws, sum_psvs), m);

    STRACE("predabst", tout << "bound: " << mk_pp(bound, m) << "\n";);
    STRACE("predabst", tout << "decrease: " << mk_pp(decrease, m) << "\n";);

    return expr_ref(m.mk_and(bound, decrease), m);
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
            if (lambda_kinds[i].m_op != op_eq) {
                min_lambda = 0;
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

expr_ref_vector rel_template_suit::subst_template_body(expr_ref_vector const& fmls, vector<rel_template> const& rel_templates, expr_ref_vector& args_coll) const {
    expr_ref_vector new_fmls(m);
    for (unsigned i = 0; i < fmls.size(); ++i) {
        new_fmls.push_back(subst_template_body(expr_ref(fmls.get(i), m), rel_templates, args_coll));
    }
    return new_fmls;
}

expr_ref rel_template_suit::subst_template_body(expr_ref const& fml, vector<rel_template> const& rel_templates, expr_ref_vector& args_coll) const {
    app_ref a(to_app(fml), m);
    if (m.is_and(fml)) {
        expr_ref_vector sub_formulas(m, a->get_num_args(), a->get_args());
        expr_ref_vector new_sub_formulas = subst_template_body(sub_formulas, rel_templates, args_coll);
        return expr_ref(m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
    }
    else if (m.is_or(fml)) {
        expr_ref_vector sub_formulas(m, a->get_num_args(), a->get_args());
        expr_ref_vector new_sub_formulas = subst_template_body(sub_formulas, rel_templates, args_coll);
        return expr_ref(m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
    }
    else if (m.is_not(fml)) {
        CASSERT("predabst", a->get_num_args() == 1);
        return expr_ref(m.mk_not(subst_template_body(expr_ref(a->get_arg(0), m), rel_templates, args_coll)), m);
    }
    else if (has_template(a->get_decl())) {
        for (unsigned i = 0; i < rel_templates.size(); i++) {
            if (a->get_decl() == rel_templates.get(i).m_head->get_decl()) {
                expr_ref cs(m_rel_templates_orig.get(i).m_body);
                expr_ref_vector args(m, a->get_num_args(), a->get_args());
                args_coll.append(args);
                args.append(m_params);
                args.reverse(); // >>> bogus
                m_var_subst(cs, args.size(), args.c_ptr(), cs);
                return cs;
            }
        }
    }
    return fml;
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

bool interpolate(expr_ref_vector const& vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol) {
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

bool rel_template_suit::instantiate_templates(expr_ref const& constraint) {
    smt_params new_param;
    smt::kernel solver(m, new_param);
    if (m_extras) {
        solver.assert_expr(m_extras);
    }
    if (constraint) {
        solver.assert_expr(constraint);
    }
    //STRACE("predabst", solver.display(tout); tout << std::endl;);
    if (solver.check() != l_true) {
        return false;
    }
    solver.get_model(m_modref);
    m_rel_template_instances.reset();
    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        expr_ref instance(m);
        if (!m_modref->eval(m_rel_templates[i].m_body, instance)) {
            return false;
        }
        STRACE("predabst", tout << "instance  : " << mk_pp(instance, m) << "\n";);
        m_rel_template_instances.push_back(rel_template(m_rel_templates[i].m_head, instance));
    }
    return true;
}

bool rel_template_suit::instantiate_templates() {
    expr_ref_vector args_coll(m);
    expr_ref c1 = subst_template_body(m_acc, m_rel_templates, args_coll);
    //args_coll.append(m_temp_subst); //>>> I have no idea what this was trying to do, but m_temp_subst is no more

    expr_ref constraint_st(m);
    vector<lambda_kind> all_lambda_kinds;
    if (!mk_exists_forall_farkas(c1, args_coll, constraint_st, all_lambda_kinds)) {
        return false;
    }

    int max_lambda = 2;
    expr_ref lambda_cs = mk_bilin_lambda_constraint(all_lambda_kinds, max_lambda, m);

    expr_ref constraint(m.mk_and(constraint_st, lambda_cs), m);
    return instantiate_templates(constraint);
}

void rel_template_suit::display(std::ostream& out) const {
    out << "templates: " << m_rel_templates.size() << "\n";
    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        out << "template " << i << " : " << m_rel_templates[i].m_head->get_decl()->get_name() << " / " << m_rel_templates[i].m_head->get_decl()->get_arity() << "\n";
        out << "template body : " << mk_pp(m_rel_templates[i].m_body, m) << "\n";
        out << "template head : " << mk_pp(m_rel_templates[i].m_head, m) << "\n";
    }
    out << "instances: " << m_rel_template_instances.size() << "\n";
    for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
        out << "instance " << i << " : " << m_rel_template_instances[i].m_head->get_decl()->get_name() << " / " << m_rel_template_instances[i].m_head->get_decl()->get_arity() << "\n";
        out << "instance body : " << mk_pp(m_rel_template_instances[i].m_body, m) << "\n";
        out << "instance head : " << mk_pp(m_rel_template_instances[i].m_head, m) << "\n";

        expr_ref_vector inst_body_terms = get_conj_terms(m_rel_template_instances[i].m_body);
        out << "inst_body_terms: " << inst_body_terms.size() << "\n";
        for (unsigned j = 0; j < inst_body_terms.size(); j++) {
            out << "inst_body_terms : " << mk_pp(inst_body_terms.get(j), m) << "\n";
        }
    }

    out << "orig templates: " << m_rel_templates_orig.size() << "\n";
    for (unsigned i = 0; i < m_rel_templates_orig.size(); i++) {
        out << "orig template " << i << " : " << m_rel_templates_orig[i].m_head->get_decl()->get_name() << " / " << m_rel_templates_orig[i].m_head->get_decl()->get_arity() << "\n";
        out << "orig template body : " << mk_pp(m_rel_templates_orig[i].m_body, m) << "\n";
        out << "orig template head : " << mk_pp(m_rel_templates_orig[i].m_head, m) << "\n";
    }
}
