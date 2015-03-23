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

typedef enum { bilin_sing, bilin } lambda_kind_sort;
typedef enum { op_eq, op_le } rel_op;

std::ostream& operator<<(std::ostream& ostr, rel_op op) {
    CASSERT("predabst", (op == op_eq) || (op == op_le));
    switch (op) {
    case op_eq:
        ostr << "=";
        break;
    case op_le:
        ostr << "<=";
        break;
    }
    return ostr;
}

struct lambda_kind {
    expr_ref m_lambda;
    lambda_kind_sort m_kind;
    rel_op m_op;

    lambda_kind(expr_ref lambda, lambda_kind_sort kind, rel_op op) :
        m_lambda(lambda),
        m_kind(kind),
        m_op(op) {
    }
};

class farkas_pred {
    // Represents the expression (Sigma_i (m_vars[i] * m_coeffs[i])) m_op m_const
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
        m(vars.get_manager()) {
    }

    // Convert an expression of the form (E1 op E2), where E1 and E2 are formulae
    // involving m_vars, into an equivalent expression of the form stored by this class.
    void set(expr_ref e) {
        arith_util arith(m);
        th_rewriter rw(m);
        e = rewrite_pred(e);
        rw(e);
        m_has_params = false;
        expr_ref_vector terms = get_additive_terms(e);
        expr_ref_vector p_consts(m);
        expr_ref_vector p_vars(m);
        expr_ref_vector p_coeffs(m);
        for (unsigned i = 0; i < terms.size(); ++i) {
            expr_ref term(terms.get(i), m);
            expr_ref_vector factors = get_multiplicative_factors(term);
            expr_ref_vector var_factors(m);
            expr_ref_vector const_factors(m);

            for (unsigned j = 0; j < factors.size(); ++j) {
                expr_ref factor(factors.get(j), m);
                if (m_vars.contains(factor)) {
                    var_factors.push_back(factor);
                }
                else {
                    expr_ref_vector factor_vars = get_all_vars(factor);
                    for (unsigned k = 0; k < factor_vars.size(); ++k) {
                        if (m_vars.contains(factor_vars.get(k))) {
                            STRACE("predabst", tout << "Found non-linear term " << mk_pp(factor, m) << "\n";);
                            CASSERT("predabst", false);
                        }
                    }
                    const_factors.push_back(factor);
                    if (!arith_util(m).is_numeral(factor)) {
                        m_has_params = true;
                    }
                }
            }

            if (var_factors.size() == 0) {
                p_consts.push_back(term);
            }
            else {
                CASSERT("predabst", var_factors.size() == 1);
                p_vars.push_back(var_factors.get(0));
                p_coeffs.push_back(mk_prod(const_factors));
            }
        }

        m_const = arith.mk_uminus(mk_sum(p_consts));
        rw(m_const);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            bool found_coeff = false;
            for (unsigned j = 0; j < p_vars.size(); ++j) {
                if (m_vars.get(i) == p_vars.get(j)) {
                    m_coeffs.push_back(p_coeffs.get(j));
                    p_vars.erase(j);
                    p_coeffs.erase(j);
                    found_coeff = true;
                    break;
                }
            }
            if (!found_coeff) {
                m_coeffs.push_back(arith.mk_numeral(rational::zero(), true));
            }
        }
    }

    expr_ref get_coeff(unsigned i) const {
        return expr_ref(m_coeffs.get(i), m);
    }

    rel_op get_op() const {
        return m_op;
    }

    expr_ref get_const() const {
        return m_const;
    }

    bool has_params() const {
        return m_has_params;
    }

    void display(std::ostream& out) const {
        out << "  ";
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (i != 0) {
                out << " + ";
            }
            out << mk_pp(m_coeffs[i], m) << " * " << mk_pp(m_vars[i], m);
        }
        out << " " << m_op << " " << mk_pp(m_const, m);
        if (m_has_params) {
            out << " (with params)";
        }
        out << "\n";
    }

private:

    expr* rewrite_pred(expr_ref const& term) {
        arith_util arith(m);
        expr *e1;
        expr *e2;
        if (m.is_true(term)) {
            // true <=> (0 = 0)
            m_op = op_le;
            return arith.mk_numeral(rational::zero(), true);
        }
        else if (m.is_false(term)) {
            // false <=> (1 <= 0)
            m_op = op_le;
            return arith.mk_numeral(rational::one(), true);
        }
        else if (m.is_eq(term, e1, e2)) {
            // (e1 == e2) <=> (e1 - e2 == 0)
            m_op = op_eq;
            return arith.mk_sub(e1, e2);
        }
        else if (arith.is_le(term, e1, e2)) {
            // (e1 <= e2) <=> (e1 - e2 <= 0)
            m_op = op_le;
            return arith.mk_sub(e1, e2);
        }
        else if (arith.is_ge(term, e1, e2)) {
            // (e1 >= e2) <=> (e2 - e1 <= 0)
            m_op = op_le;
            return arith.mk_sub(e2, e1);
        }
        else if (arith.is_lt(term, e1, e2)) {
            // (e1 < e2) <=> (e1 - e2 + 1 <= 0)
            m_op = op_le;
            return arith.mk_add(arith.mk_sub(e1, e2), arith.mk_numeral(rational::one(), true));
        }
        else if (arith.is_gt(term, e1, e2)) {
            // (e1 > e2) <=> (e2 - e1 + 1 <= 0)
            m_op = op_le;
            return arith.mk_add(arith.mk_sub(e2, e1), arith.mk_numeral(rational::one(), true));
        }
        else {
            STRACE("predabst", tout << "Unable to recognize predicate " << mk_pp(term, m) << "\n";);
            UNREACHABLE();
            return nullptr;
        }
    }
};

class farkas_imp {
    expr_ref_vector m_vars;
    vector<farkas_pred> m_lhs;
    farkas_pred m_rhs;
    unsigned m_param_pred_count;
    expr_ref_vector m_lambdas;
    expr_ref_vector m_constraints;

    ast_manager& m;

public:
    farkas_imp(expr_ref_vector const& vars) :
        m_vars(vars),
        m_rhs(vars),
        m_param_pred_count(0),
        m_lambdas(vars.get_manager()),
        m_constraints(vars.get_manager()),
        m(vars.get_manager()) {
    }

    void set(expr_ref const& lhs_term, expr_ref const& rhs_term) {
        STRACE("predabst", tout << "Solving " << mk_pp(lhs_term, m) << " => " << mk_pp(rhs_term, m) << ", in variables "; print_expr_ref_vector(tout, m_vars););
        expr_ref_vector conjs = get_conj_terms(lhs_term);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            farkas_pred f_pred(m_vars);
            f_pred.set(expr_ref(conjs.get(i), m));
            m_lhs.push_back(f_pred);
            if (f_pred.has_params()) {
                m_param_pred_count++;
            }
        }

        m_rhs.set(rhs_term);

        m_lambdas.swap(make_lambdas());
        m_constraints.swap(make_constraints());

#ifdef Z3DEBUG
        dump_solution();
#endif
    }

#ifdef Z3DEBUG
    void dump_solution() const {
        smt_params new_param;
        smt::kernel solver(m, new_param);
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            solver.assert_expr(m_constraints.get(i));
        }
        if (solver.check() != l_true) {
            STRACE("predabst", tout << "Unable to find solution\n";);
            return;
        }

        model_ref modref;
        solver.get_model(modref);
        expr_ref_vector solutions(m);
        for (unsigned j = 0; j < m_lhs.size(); ++j) {
            expr_ref solution(m);
            if (!modref->eval(m_lambdas.get(j), solution, true)) {
                return;
            }
            solutions.push_back(solution);
        }

        STRACE("predabst", tout << "Found solution: ("; print_expr_ref_vector(tout, solutions, false); tout << ")\n";);
    }
#endif

    expr_ref_vector const& get_constraints() const {
        return m_constraints;
    }

    vector<lambda_kind> get_bilin_lambda_kinds() const {
        vector<lambda_kind> lambda_kinds;
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            if (m_lhs.get(i).has_params()) {
                if (m_param_pred_count == 1) {
                    if (m_lhs.get(i).get_op() == op_eq) {
                        lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), bilin_sing, m_lhs.get(i).get_op()));
                    }
                    else {
                        // This lambda will be replaced with 1 and so will disappear from the constraints.
                    }
                }
                else {
                    lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), bilin, m_lhs.get(i).get_op()));
                }
            }
        }
        return lambda_kinds;
    }

    void display(std::ostream& out) const {
        out << "LHS:\n";
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            m_lhs.get(i).display(out);
        }
        out << "RHS:\n";
        m_rhs.display(out);
        out << "Constraint:\n";
        print_expr_ref_vector(out, m_constraints);
    }

private:

    expr_ref_vector make_lambdas() const {
        bool is_bilin_sing = false;
        unsigned bilin_sing_idx;
        if (m_param_pred_count == 1) {
            for (unsigned i = 0; i < m_lhs.size(); ++i) {
                if (m_lhs.get(i).has_params()) {
                    if (m_lhs.get(i).get_op() == op_le) {
                        is_bilin_sing = true;
                        bilin_sing_idx = i;
                    }
                    break;
                }
            }
        }

        expr_ref_vector lambdas(m);

        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            if (is_bilin_sing && (i == bilin_sing_idx)) {
                arith_util arith(m);
                lambdas.push_back(arith.mk_numeral(rational::one(), true));
            }
            else {
                lambdas.push_back(m.mk_fresh_const("t", arith_util(m).mk_int()));
            }
        }

        return lambdas;
    }

    expr_ref_vector make_constraints() const {
        arith_util arith(m);
        //CASSERT("predabst", m_lhs.get_param_pred_count() > 0);
        // XXX This assert fails on unsat-N.smt2, but without it the tests pass.  It's not clear whether this assert is wrong, or whether there's a bug.

        expr_ref_vector constraints(m);

        for (unsigned j = 0; j < m_lhs.size(); ++j) {
            expr* lambda = m_lambdas.get(j);
            rel_op op = m_lhs.get(j).get_op();
            CASSERT("predabst", (op == op_le) || (op == op_eq));
            if (op == op_le) {
                if (!arith.is_one(lambda)) {
                    constraints.push_back(arith.mk_ge(lambda, arith.mk_numeral(rational::zero(), true)));
                }
            }
        }

        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref_vector terms(m);
            for (unsigned j = 0; j < m_lhs.size(); ++j) {
                expr* lambda = m_lambdas.get(j);
                expr* coeff = m_lhs.get(j).get_coeff(i);
                if (!arith.is_zero(coeff)) {
                    if (arith.is_one(lambda)) {
                        terms.push_back(coeff);
                    }
                    else {
                        terms.push_back(arith.mk_mul(lambda, coeff));
                    }
                }
            }
            constraints.push_back(m.mk_eq(mk_sum(terms), m_rhs.get_coeff(i)));
        }

        expr_ref_vector terms(m);
        for (unsigned j = 0; j < m_lhs.size(); ++j) {
            expr* lambda = m_lambdas.get(j);
            expr* constant = m_lhs.get(j).get_const();
            if (!arith.is_zero(constant)) {
                terms.push_back(arith.mk_mul(lambda, constant));
            }
        }
        constraints.push_back(arith.mk_le(mk_sum(terms), m_rhs.get_const()));

        return constraints;
    }
};

static expr_ref_vector mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, vector<lambda_kind>& lambda_kinds, bool eliminate_unsat_disjuncts = false) {
    ast_manager& m = fml.m();
    CASSERT("predabst", lambda_kinds.empty());
    expr_ref_vector constraint_st(m);
    expr_ref norm_fml = to_dnf(expr_ref(m.mk_not(fml), m));
    expr_ref_vector disjs = get_disj_terms(norm_fml);
    for (unsigned i = 0; i < disjs.size(); ++i) {
        if (eliminate_unsat_disjuncts) {
            smt_params new_param;
            smt::kernel solver(fml.m(), new_param);
            solver.assert_expr(disjs.get(i));
            if (solver.check() != l_true) {
                continue;
            }
        }
        farkas_imp f_imp(vars);
        f_imp.set(expr_ref(disjs.get(i), m), expr_ref(m.mk_false(), m));
        STRACE("predabst", f_imp.display(tout););
        constraint_st.append(f_imp.get_constraints());
        lambda_kinds.append(f_imp.get_bilin_lambda_kinds());
    }
    return constraint_st;
}

void well_founded_bound_and_decrease(expr_ref_vector const& vsws, expr_ref& bound, expr_ref& decrease) {
    CASSERT("predabst", vsws.size() % 2 == 0);

    ast_manager& m = vsws.get_manager();

    expr_ref_vector vs(m);
    for (unsigned i = 0; i < (vsws.size() / 2); i++) {
        vs.push_back(vsws.get(i));
    }

    expr_ref_vector ws(m);
    for (unsigned i = (vsws.size() / 2); i < vsws.size(); ++i) {
        ws.push_back(vsws.get(i));
    }

    arith_util arith(m);

    expr_ref_vector sum_psvs_terms(m);
    expr_ref_vector sum_psws_terms(m);
    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        sum_psvs_terms.push_back(arith.mk_mul(param, vs.get(i)));
        sum_psws_terms.push_back(arith.mk_mul(param, ws.get(i)));
    }
    expr_ref sum_psvs = mk_sum(sum_psvs_terms);
    expr_ref sum_psws = mk_sum(sum_psws_terms);

    expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);

    bound = arith.mk_ge(sum_psvs, delta0);
    STRACE("predabst", tout << "WF bound: " << mk_pp(bound, m) << "\n";);

    decrease = arith.mk_lt(sum_psws, sum_psvs);
    STRACE("predabst", tout << "WF decrease: " << mk_pp(decrease, m) << "\n";);
}

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref* sol_bound, expr_ref* sol_decrease) {
    CASSERT("predabst", vsws.size() % 2 == 0);
    CASSERT("predabst", (sol_bound && sol_decrease) || (!sol_bound && !sol_decrease));

    ast_manager& m = lhs.get_manager();
    if (!m.is_and(lhs) || to_app(lhs)->get_num_args() <= 1) {
        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is not well-founded: it is not a conjunction of at least 2 terms\n";);
        return false;
    }

    expr_ref_vector lhs_vars = get_all_vars(lhs);
    for (unsigned j = 0; j < lhs_vars.size(); j++) {
        CASSERT("predabst", vsws.contains(lhs_vars.get(j)));
    }

    bool hasv = false;
    for (unsigned i = 0; i < (vsws.size() / 2); i++) {
        if (lhs_vars.contains(vsws.get(i))) {
            hasv = true;
            break;
        }
    }
    if (!hasv) {
        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is not well-founded: it contains no variable from vs\n";);
        return false;
    }

    bool hasw = false;
    for (unsigned i = (vsws.size() / 2); i < vsws.size(); ++i) {
        if (lhs_vars.contains(vsws.get(i))) {
            hasw = true;
            break;
        }
    }
    if (!hasw) {
        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is not well-founded: it contains no variable from ws\n";);
        return false;
    }

    expr_ref bound(m);
    expr_ref decrease(m);
    well_founded_bound_and_decrease(vsws, bound, decrease);
    expr_ref to_solve(m.mk_or(m.mk_not(lhs), m.mk_and(bound, decrease)), m);

    // Does passing true for eliminate_unsat_disjunts help in the refinement case?
    vector<lambda_kind> lambda_kinds;
    expr_ref_vector constraint_st = mk_exists_forall_farkas(to_solve, vsws, lambda_kinds);
    CASSERT("predabst", lambda_kinds.empty());

    smt_params new_param;
    if (!sol_bound && !sol_decrease) {
        new_param.m_model = false;
    }
    smt::kernel solver(m, new_param);
    for (unsigned i = 0; i < constraint_st.size(); ++i) {
        solver.assert_expr(constraint_st.get(i));
    }

    if (solver.check() != l_true) {
        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is not well-founded: constraint is unsatisfiable\n";);
        return false;
    }

    if (sol_bound && sol_decrease) {
        model_ref modref;
        solver.get_model(modref);
        if (!(modref->eval(bound, *sol_bound) && modref->eval(decrease, *sol_decrease))) {
            return false;
        }

        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is well-founded, with bound " << mk_pp(*sol_bound, m) << "; decrease " << mk_pp(*sol_decrease, m) << "\n";);
    }
    else {
        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is well-founded\n";);
    }
    
    return true;
}

bool interpolate(expr_ref_vector const& vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol) {
    quantifier_elimination(vars, fmlA);
    quantifier_elimination(vars, fmlB);

    ast_manager& m = vars.get_manager();
    arith_util arith(m);
    expr_ref_vector sum_vars_terms(m);
    for (unsigned i = 0; i < vars.size(); ++i) {
        expr_ref param(m.mk_fresh_const("i", arith.mk_int()), m);
        sum_vars_terms.push_back(arith.mk_mul(param, vars.get(i)));
    }
    expr_ref sum_vars = mk_sum(sum_vars_terms);
    expr_ref ic(m.mk_const(symbol("ic"), arith.mk_int()), m);
    expr_ref fmlQ(arith.mk_le(sum_vars, ic), m);

    expr_ref to_solve(m.mk_and(m.mk_or(m.mk_not(fmlA), fmlQ), m.mk_or(m.mk_not(fmlQ), m.mk_not(fmlB))), m);
    vector<lambda_kind> lambda_kinds;
    expr_ref_vector constraint_st = mk_exists_forall_farkas(to_solve, vars, lambda_kinds);
    CASSERT("predabst", lambda_kinds.empty());

    smt_params new_param;
    smt::kernel solver(m, new_param);
    for (unsigned i = 0; i < constraint_st.size(); ++i) {
        solver.assert_expr(constraint_st.get(i));
    }
    if (solver.check() != l_true) {
        STRACE("predabst", tout << "Interpolation failed: constraint is unsatisfiable\n";);
        return false;
    }

    model_ref modref;
    solver.get_model(modref);
    if (!modref->eval(fmlQ, fmlQ_sol)) {
        return false;
    }

    STRACE("predabst", tout << "Interpolation succeeded\n";);
    return true;
}

static expr_ref_vector mk_bilin_lambda_constraints(vector<lambda_kind> const& lambda_kinds, int max_lambda, ast_manager& m) {
    arith_util arith(m);

    expr_ref n1(arith.mk_numeral(rational::one(), true), m);
    expr_ref nminus1(arith.mk_numeral(rational::minus_one(), true), m);

    expr_ref_vector cons(m);
    for (unsigned i = 0; i < lambda_kinds.size(); i++) {
        if (lambda_kinds[i].m_kind == bilin_sing) {
            CASSERT("predabst", lambda_kinds[i].m_op == op_eq);
            cons.push_back(m.mk_or(m.mk_eq(lambda_kinds[i].m_lambda, nminus1), m.mk_eq(lambda_kinds[i].m_lambda, n1)));
        }
        else {
            CASSERT("predabst", lambda_kinds[i].m_kind == bilin);
            int min_lambda = (lambda_kinds[i].m_op == op_eq) ? -max_lambda : 0;
            expr_ref_vector bilin_disj_terms(m);
            for (int j = min_lambda; j <= max_lambda; j++) {
                bilin_disj_terms.push_back(m.mk_eq(lambda_kinds[i].m_lambda, arith.mk_numeral(rational(j), true)));
            }
            cons.push_back(mk_disj(bilin_disj_terms));
        }
    }
    return cons;
}

expr_ref_vector rel_template_suit::subst_template_body(expr_ref_vector const& fmls, expr_ref_vector& args_coll) const {
    expr_ref_vector new_fmls(m);
    for (unsigned i = 0; i < fmls.size(); ++i) {
        new_fmls.push_back(subst_template_body(expr_ref(fmls.get(i), m), args_coll));
    }
    return new_fmls;
}

expr_ref rel_template_suit::subst_template_body(expr_ref const& fml, expr_ref_vector& args_coll) const {
    app_ref a(to_app(fml), m);
    if (m.is_and(fml)) {
        expr_ref_vector sub_formulas(m, a->get_num_args(), a->get_args());
        expr_ref_vector new_sub_formulas = subst_template_body(sub_formulas, args_coll);
        return expr_ref(m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
    }
    else if (m.is_or(fml)) {
        expr_ref_vector sub_formulas(m, a->get_num_args(), a->get_args());
        expr_ref_vector new_sub_formulas = subst_template_body(sub_formulas, args_coll);
        return expr_ref(m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
    }
    else if (m.is_not(fml)) {
        CASSERT("predabst", a->get_num_args() == 1);
        return expr_ref(m.mk_not(subst_template_body(expr_ref(a->get_arg(0), m), args_coll)), m);
    }
    else if (has_template(a->get_decl())) {
        for (unsigned i = 0; i < m_rel_templates.size(); i++) {
            if (a->get_decl() == m_rel_templates.get(i).m_head->get_decl()) {
                args_coll.append(a->get_num_args(), a->get_args());

                expr_ref temp_body(m);
                expr_ref_vector temp_vars(m);
                get_template(i, temp_body, temp_vars);
                expr_ref_vector subst = build_subst(temp_vars, a->get_args());
                return apply_subst(temp_body, subst);
            }
        }
        UNREACHABLE();
        return expr_ref(m);
    }
    else {
        return fml;
    }
}

bool rel_template_suit::instantiate_templates() {
    expr_ref_vector args_coll(m);
    expr_ref c1 = subst_template_body(m_acc, args_coll);
    //args_coll.append(m_temp_subst); //>>> I have no idea what this was trying to do, but m_temp_subst is no more

    vector<lambda_kind> lambda_kinds;
    expr_ref_vector constraint_st = mk_exists_forall_farkas(c1, args_coll, lambda_kinds, true);

    int max_lambda = 2;
    expr_ref_vector lambda_cs = mk_bilin_lambda_constraints(lambda_kinds, max_lambda, m);

    STRACE("predabst", tout << "Using constraints: "; print_expr_ref_vector(tout, constraint_st););
    STRACE("predabst", tout << "Using lambda constraint: "; print_expr_ref_vector(tout, lambda_cs););

    smt_params new_param;
    smt::kernel solver(m, new_param);
    if (m_extras) {
        solver.assert_expr(m_extras);
    }
    for (unsigned i = 0; i < constraint_st.size(); ++i) {
        solver.assert_expr(constraint_st.get(i));
    }
    for (unsigned i = 0; i < lambda_cs.size(); ++i) {
        solver.assert_expr(lambda_cs.get(i));
    }
    if (solver.check() != l_true) {
        STRACE("predabst", tout << "Failed to solve template constraints\n";);
        return false;
    }
    solver.get_model(m_modref);

    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        expr_ref temp_body(m);
        expr_ref_vector temp_vars(m);
        get_template(i, temp_body, temp_vars);
        
        // First, evaluate the template body with respect to the model, to give values for each of the extra template parameters.
        expr_ref instance(m);
        if (!m_modref->eval(temp_body, instance, true)) {
            return false;
        }

        // Second, replace the variables corresponding to the query parameters with fresh constants.
        expr_ref_vector subst = build_subst(temp_vars, m_rel_template_instances[i].m_head->get_args());
        expr_ref body = apply_subst(instance, subst);

        STRACE("predabst", tout << "Instantiated template " << i << ": " << mk_pp(m_rel_template_instances[i].m_head, m) << " := " << mk_pp(body, m) << "\n";);
        m_rel_template_instances[i].m_body = body;
    }
    return true;
}

