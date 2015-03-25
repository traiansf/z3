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
#include "farkas_util.h"
#include "predabst_util.h"
#include "well_sorted.h"
#include "th_rewriter.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "smt_kernel.h"
#include "smt_params.h"

std::ostream& operator<<(std::ostream& out, rel_op op) {
    switch (op) {
    case op_eq:
        out << "=";
        break;
    case op_le:
        out << "<=";
        break;
    default:
        UNREACHABLE();
        break;
    }
    return out;
}

static unsigned count_bilinear(vector<lambda_info> const& lambdas) {
    unsigned num_bilinear = 0;
    for (unsigned i = 0; i < lambdas.size(); i++) {
        if (lambdas[i].m_kind == bilinear) {
            ++num_bilinear;
        }
    }
    return num_bilinear;
}

static unsigned count_bilinear_uninterp_const(vector<lambda_info> const& lambdas) {
    unsigned num_bilinear_uninterp_const = 0;
    for (unsigned i = 0; i < lambdas.size(); i++) {
        if ((lambdas[i].m_kind == bilinear) && is_uninterp_const(lambdas[i].m_lambda)) {
            ++num_bilinear_uninterp_const;
        }
    }
    return num_bilinear_uninterp_const;
}

// Rewrites a binary (in)equality (E1 op E2) to be of the form (E' op' 0),
// where op' is either = or <=.
static bool rewrite_inequality(expr_ref const& e, expr_ref& new_e, rel_op& new_op) {
    ast_manager& m = e.m();
    arith_util arith(m);

    expr *e1;
    expr *e2;
    if (m.is_eq(e, e1, e2)) {
        // (e1 == e2) <=> (e1 - e2 == 0)
        new_e = arith.mk_sub(e1, e2);
        new_op = op_eq;
    }
    else if (arith.is_le(e, e1, e2)) {
        // (e1 <= e2) <=> (e1 - e2 <= 0)
        new_e = arith.mk_sub(e1, e2);
        new_op = op_le;
    }
    else if (arith.is_ge(e, e1, e2)) {
        // (e1 >= e2) <=> (e2 - e1 <= 0)
        new_e = arith.mk_sub(e2, e1);
        new_op = op_le;
    }
    else if (arith.is_lt(e, e1, e2)) {
        // (e1 < e2) <=> (e1 - e2 + 1 <= 0)
        new_e = arith.mk_add(arith.mk_sub(e1, e2), arith.mk_numeral(rational::one(), true));
        new_op = op_le;
    }
    else if (arith.is_gt(e, e1, e2)) {
        // (e1 > e2) <=> (e2 - e1 + 1 <= 0)
        new_e = arith.mk_add(arith.mk_sub(e2, e1), arith.mk_numeral(rational::one(), true));
        new_op = op_le;
    }
    else {
        STRACE("predabst", tout << "Expression is not a binary (in)equality: " << mk_pp(e, m) << "\n";);
        return false;
    }

    if (get_sort(e1) != arith.mk_int()) {
        STRACE("predabst", tout << "Operands of (in)equality are not integers: " << mk_pp(e, m) << "\n";);
        return false;
    }

    return true;
}

class linear_inequality {
    // Represents a linear (in)equality in the variables m_vars.
    //
    // Specifically, represents the (in)equality:
    //     (Sigma_i (m_vars[i] * m_coeffs[i])) m_op m_const
    // where m_vars are distinct (grounded) variables, and m_coeffs and
    // m_const do not contain any of those variables.

    expr_ref_vector const m_vars;
    expr_ref_vector m_coeffs;
    rel_op m_op;
    expr_ref m_const;

    bool m_has_params; // true if m_coeffs or m_const contain any uninterpreted constants
    
    ast_manager& m;

public:

    linear_inequality(expr_ref_vector const& vars) :
        m_vars(vars),
        m_coeffs(vars.get_manager()),
        m_const(vars.get_manager()),
        m(vars.get_manager()) {
    }

    // Convert an (in)equality of the form (E1 op E2), where E1 and E2 are formulae
    // involving m_vars, into an equivalent expression of the form stored by this class.
    // Returns false if this is impossible, i.e. if the (in)equality is not linear in
    // m_vars.
    bool set(expr_ref e) {
        CASSERT("predabst", is_well_sorted(m, e));
        arith_util arith(m);
        th_rewriter rw(m);

        m_coeffs.reset();
        m_const.reset();
        m_has_params = false;

        // Push all terms to the LHS of the (in)equality.
        expr_ref lhs(m);
        bool result = rewrite_inequality(e, lhs, m_op);
        if (!result) {
            return false;
        }

        // Simplify the LHS of the (in)equality.  The simplified expression
        // will be a sum of terms, each of which is a product of factors.
        rw(lhs);

        // Split the terms into those which have one of the m_vars as a
        // factor (var_terms), and those which do not (const_terms), while
        // checking that all the terms are linear in m_vars.
        vector<expr_ref_vector> var_terms;
        var_terms.reserve(m_vars.size(), expr_ref_vector(m));
        expr_ref_vector const_terms(m);

        expr_ref_vector terms = get_additive_terms(lhs);
        for (unsigned i = 0; i < terms.size(); ++i) {
            expr_ref term(terms.get(i), m);
            
            // Split the factors into those which are one of the m_vars
            // (var_factors) and those which are not (const_factors).
            expr_ref_vector var_factors(m);
            expr_ref_vector const_factors(m);

            expr_ref_vector factors = get_multiplicative_factors(term);
            for (unsigned j = 0; j < factors.size(); ++j) {
                expr_ref factor(factors.get(j), m);
                if (m_vars.contains(factor)) {
                    var_factors.push_back(factor);
                }
                else {
                    expr_ref_vector factor_vars = get_all_vars(factor);
                    for (unsigned k = 0; k < factor_vars.size(); ++k) {
                        if (m_vars.contains(factor_vars.get(k))) {
                            STRACE("predabst", tout << "Found non-linear factor " << mk_pp(factor, m) << "\n";);
                            return false;
                        }
                    }
                    if (!factor_vars.empty()) {
                        m_has_params = true;
                    }
                    const_factors.push_back(factor);
                }
            }

            if (var_factors.size() == 0) {
                const_terms.push_back(term);
            }
            else if (var_factors.size() == 1) {
                unsigned j = vector_find(m_vars, var_factors.get(0));
                var_terms[j].push_back(mk_prod(const_factors));
            }
            else {
                STRACE("predabst", tout << "Found non-linear term " << mk_pp(term, m) << "\n";);
                return false;
            }
        }

        // Move the constant terms to the RHS of the (inequality).
        m_const = arith.mk_uminus(mk_sum(const_terms));
        rw(m_const);

        for (unsigned i = 0; i < m_vars.size(); ++i) {
            m_coeffs.push_back(mk_sum(var_terms.get(i)));
        }

        return true;
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

    friend std::ostream& operator<<(std::ostream& out, linear_inequality const& lineq);
};

std::ostream& operator<<(std::ostream& out, linear_inequality const& lineq) {
    ast_manager& m = lineq.m;
    for (unsigned i = 0; i < lineq.m_vars.size(); ++i) {
        if (i != 0) {
            out << " + ";
        }
        out << mk_pp(lineq.m_coeffs[i], m) << " * " << mk_pp(lineq.m_vars[i], m);
    }
    out << " " << lineq.m_op << " " << mk_pp(lineq.m_const, m);
    if (lineq.m_has_params) {
        out << " (has params)";
    }
    return out;
}

class farkas_imp {
    // Represents an implication from a set of linear (in)equalities to
    // another liner inequality, where all the (in)equalities are linear
    // in a common set of variables (m_vars).
    //
    // Symbolically:
    //
    //   (A . v <= b) ==> (c . v <= d)
    //
    // Or graphically:
    //
    //   (. . .) (.)    (.)               (.)
    //   (. A .) (v) <= (b)  ==>  (. c .) (v) <= d
    //   (. . .) (.)    (.)               (.)
    //
    // Farkas's lemma says that this implication holds if and only if
    // the inequality on the RHS is a consequence of a linear combination
    // of the inequalities on the LHS, where the multipliers of all
    // inequalities on the LHS must be non-negative.  That is:
    //
    //     Forall v, (A . v <= b) ==> (c . v <= d)
    //   <==>
    //     Exists lambda, (lambda >= 0), (lambda . A = c) AND (lambda . b <= d)
    //
    // If any of (in)equalities on the LHS are actually equalities,
    // then the constraint on that lambda may be dropped.

    expr_ref_vector const m_vars;
    vector<linear_inequality> m_lhs;
    linear_inequality m_rhs;
    expr_ref_vector m_lambdas;

    ast_manager& m;

public:
    farkas_imp(expr_ref_vector const& vars) :
        m_vars(vars),
        m_rhs(vars),
        m_lambdas(vars.get_manager()),
        m(vars.get_manager()) {
    }

    bool set(expr_ref_vector const& lhs_terms, expr_ref const& rhs_term) {
        STRACE("predabst", tout << "Solving " << lhs_terms << " => " << mk_pp(rhs_term, m) << ", in variables " << m_vars << "\n";);
        m_lhs.reset();
        for (unsigned i = 0; i < lhs_terms.size(); ++i) {
            linear_inequality lineq(m_vars);
            bool result = lineq.set(expr_ref(lhs_terms.get(i), m));
            if (!result) {
                return false;
            }
            m_lhs.push_back(lineq);
        }

        bool result = m_rhs.set(rhs_term);
        if (!result) {
            return false;
        }

        if (m_rhs.get_op() == op_eq) {
            STRACE("predabst", tout << "RHS is an equality not an inequality\n";);
            return false;
        }

        m_lambdas.swap(make_lambdas());

        return true;
    }

    expr_ref_vector get_constraints() const {
        arith_util arith(m);

        expr_ref_vector constraints(m);

        // The multipliers for all inequalities (as opposed to equalities)
        // must be non-negative.
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

        // lambda . A = c
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

        // lambda . b <= d
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

    vector<lambda_info> get_lambdas() const {
        vector<lambda_info> lambdas;
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            lambda_kind kind = m_lhs.get(i).has_params() ? bilinear : linear;
            lambdas.push_back(lambda_info(expr_ref(m_lambdas.get(i), m), kind, m_lhs.get(i).get_op()));
        }
        return lambdas;
    }

    void display(std::ostream& out) const {
        out << "LHS:\n";
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            out << "  " << mk_pp(m_lambdas.get(i), m) << ": " << m_lhs.get(i) << std::endl;
        }
        out << "RHS:\n";
        out << "  " << m_rhs << std::endl;
    }

private:

    expr_ref_vector make_lambdas() const {
        // We classify the (in)equalities on the LHS as either 'linear' or
        // 'bilinear', according to whether the coefficients are all
        // integers, or whether some of the coefficients are uninterpreted
        // constants.
        unsigned num_bilinear = 0;
        unsigned bilinear_idx;
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            if (m_lhs.get(i).has_params()) {
                ++num_bilinear;
                bilinear_idx = i;
            }
        }

        expr_ref_vector lambdas(m);

        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            if ((num_bilinear == 1) && (i == bilinear_idx) && (m_lhs.get(i).get_op() == op_le)) {
                // If this is the sole bilinear (in)equality, and it is an
                // inequality, then without loss of generality we may choose
                // its multiplier to be 1.  (We cannot do this if it is an
                // equality, since the multiplier may need to be negative.)
                // This optimization reduces the problem to a purely linear
                // one.
                arith_util arith(m);
                lambdas.push_back(arith.mk_numeral(rational::one(), true));
            }
            else {
                lambdas.push_back(m.mk_fresh_const("t", arith_util(m).mk_int()));
            }
        }

        return lambdas;
    }
};

bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref_vector& constraints, vector<lambda_info>& lambdas, bool eliminate_unsat_disjuncts) {
    ast_manager& m = fml.m();
    arith_util arith(m);
    CASSERT("predabst", constraints.empty());
    CASSERT("predabst", lambdas.empty());
    expr_ref false_ineq(arith.mk_le(arith.mk_numeral(rational::one(), true), arith.mk_numeral(rational::zero(), true)), m);
    expr_ref norm_fml = to_dnf(expr_ref(m.mk_not(fml), m));
    expr_ref_vector disjs = get_disj_terms(norm_fml);
    for (unsigned i = 0; i < disjs.size(); ++i) {
        expr_ref_vector conjs = get_conj_terms(expr_ref(disjs.get(i), m));
        if (eliminate_unsat_disjuncts) {
            smt_params new_param;
            smt::kernel solver(fml.m(), new_param);
            for (unsigned j = 0; j < conjs.size(); ++j) {
                solver.assert_expr(conjs.get(j));
            }
            if (solver.check() != l_true) {
                continue;
            }
        }
        farkas_imp f_imp(vars);
        bool result = f_imp.set(conjs, false_ineq);
        if (!result) {
            STRACE("predabst", tout << "System of inequalities is non-linear\n";);
            return false;
        }
        STRACE("predabst", f_imp.display(tout););
        constraints.append(f_imp.get_constraints());
        lambdas.append(f_imp.get_lambdas());
    }
    return true;
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
    expr_ref_vector constraints(m);
    vector<lambda_info> lambdas;
    bool result = mk_exists_forall_farkas(to_solve, vsws, constraints, lambdas);
    CASSERT("predabst", result);
    CASSERT("predabst", count_bilinear_uninterp_const(lambdas) == 0);

    smt_params new_param;
    if (!sol_bound && !sol_decrease) {
        new_param.m_model = false;
    }
    smt::kernel solver(m, new_param);
    for (unsigned i = 0; i < constraints.size(); ++i) {
        solver.assert_expr(constraints.get(i));
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
    expr_ref_vector constraints(m);
    vector<lambda_info> lambdas;
    bool result = mk_exists_forall_farkas(to_solve, vars, constraints, lambdas);
    CASSERT("predabst", result);
    CASSERT("predabst", count_bilinear_uninterp_const(lambdas) == 0);

    smt_params new_param;
    smt::kernel solver(m, new_param);
    for (unsigned i = 0; i < constraints.size(); ++i) {
        solver.assert_expr(constraints.get(i));
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

expr_ref_vector mk_bilinear_lambda_constraints(vector<lambda_info> const& lambdas, int max_lambda, ast_manager& m) {
    arith_util arith(m);

    expr_ref one(arith.mk_numeral(rational::one(), true), m);
    expr_ref minus_one(arith.mk_numeral(rational::minus_one(), true), m);

    unsigned num_bilinear = count_bilinear(lambdas);

    expr_ref_vector constraints(m);
    for (unsigned i = 0; i < lambdas.size(); i++) {
        if (lambdas[i].m_kind == bilinear) {
            if (num_bilinear == 1) {
                if (lambdas[i].m_op == op_eq) {
                    // This is the sole bilinear (in)equality, and it is an
                    // equality, so without loss of generality we may choose
                    // its multiplier to be either 1 or -1.
                    constraints.push_back(m.mk_or(m.mk_eq(lambdas[i].m_lambda, minus_one), m.mk_eq(lambdas[i].m_lambda, one)));
                }
                else {
                    // This is the sole bilinear (in)equality, and it is an
                    // inequality, so the multiplier will have been set to 1
                    // above and therefore no constraint is necessary.
                    CASSERT("predabst", arith.is_one(lambdas[i].m_lambda));
                }
            }
            else {
                // There is more than one bilinear (in)equality.  In order to
                // make solving tractable, we assume that the multiplier is
                // between 0 and N for an inequality, or -N and N for an
                // equality.  Note that this assumption might prevent us from
                // finding a solution.
                int min_lambda = (lambdas[i].m_op == op_eq) ? -max_lambda : 0;
                expr_ref_vector bilin_disj_terms(m);
                for (int j = min_lambda; j <= max_lambda; j++) {
                    bilin_disj_terms.push_back(m.mk_eq(lambdas[i].m_lambda, arith.mk_numeral(rational(j), true)));
                }
                constraints.push_back(mk_disj(bilin_disj_terms));
            }
        }
    }
    return constraints;
}
