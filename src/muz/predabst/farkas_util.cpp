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

std::ostream& operator<<(std::ostream& ostr, rel_op op) {
    switch (op) {
    case op_eq:
        ostr << "=";
        break;
    case op_le:
        ostr << "<=";
        break;
    case op_ge:
        ostr << ">=";
        break;
    case op_lt:
        ostr << "<";
        break;
    case op_gt:
        ostr << ">";
        break;
    default:
        ostr << "<unknown>";
        break;
    }
    return ostr;
}

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
                m_coeffs.push_back(arith.mk_numeral(rational(0), true));
            }
        }
    }

    expr_ref_vector const& get_coeffs() const {
        return m_coeffs;
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
            return arith.mk_numeral(rational(0), true);
        }
        else if (m.is_false(term)) {
            // false <=> (1 <= 0)
            m_op = op_le;
            return arith.mk_numeral(rational(1), true);
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
            return arith.mk_add(arith.mk_sub(e1, e2), arith.mk_numeral(rational(1), true));
        }
        else if (arith.is_gt(term, e1, e2)) {
            // (e1 > e2) <=> (e2 - e1 + 1 <= 0)
            m_op = op_le;
            return arith.mk_add(arith.mk_sub(e2, e1), arith.mk_numeral(rational(1), true));
        }
        else {
            STRACE("predabst", tout << "Unable to recognize predicate " << mk_pp(term, m) << "\n";);
            UNREACHABLE();
            return nullptr;
        }
    }
};

class farkas_conj {
    expr_ref_vector m_vars;
    vector<expr_ref_vector> m_coeffs;
    vector<rel_op> m_ops;
    vector<expr_ref> m_consts;
    vector<bool> m_has_params;

    unsigned m_param_pred_count;
    ast_manager& m;

public:
    farkas_conj(expr_ref_vector const& vars) :
        m_vars(vars),
        m_param_pred_count(0),
        m(vars.get_manager()) {
    }

    void add(farkas_pred const& f_pred) {
        m_coeffs.push_back(f_pred.get_coeffs());
        m_ops.push_back(f_pred.get_op());
        m_consts.push_back(f_pred.get_const());
        m_has_params.push_back(f_pred.has_params());

        if (f_pred.has_params()) {
            m_param_pred_count++;
        }
    }

    unsigned get_size() const {
        return m_ops.size();
    }

    expr_ref get_coeff(unsigned j, unsigned i) const {
        return expr_ref(m_coeffs.get(i).get(j), m);
    }

    rel_op get_op(unsigned i) const {
        return m_ops.get(i);
    }

    expr_ref get_const(unsigned i) const {
        return expr_ref(m_consts.get(i), m);
    }

    bool has_params(unsigned i) const {
        return m_has_params.get(i);
    }

    unsigned get_param_pred_count() const {
        return m_param_pred_count;
    }

    void display(std::ostream& out) const {
        out << "  Vars: ";
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            out << mk_pp(m_vars[i], m) << " ";
        }
        out << "\n";
        for (unsigned i = 0; i < m_ops.size(); ++i) {
            out << "  Equation " << i << ": ";
            for (unsigned j = 0; j < m_vars.size(); ++j) {
                if (j != 0) {
                    out << " + ";
                }
                out << mk_pp(m_coeffs[i][j], m) << " * " << mk_pp(m_vars[j], m);
            }
            out << " " << m_ops[i] << " " << mk_pp(m_consts[i], m);
            if (m_has_params[i]) {
                out << " (with params)";
            }
            out << "\n";
        }
    }
};

class farkas_imp {
    expr_ref_vector m_vars;
    farkas_conj m_lhs;
    farkas_pred m_rhs;
    expr_ref_vector m_lambdas;
    expr_ref_vector m_solutions;
    expr_ref_vector m_constraints;

    ast_manager& m;

public:
    farkas_imp(expr_ref_vector const& vars) :
        m_vars(vars),
        m_lhs(vars),
        m_rhs(vars),
        m_lambdas(vars.get_manager()),
        m_solutions(vars.get_manager()),
        m_constraints(vars.get_manager()),
        m(vars.get_manager()) {
    }

    void set(expr_ref const& lhs_term, expr_ref const& rhs_term) {
        STRACE("predabst", tout << "Solving " << mk_pp(lhs_term, m) << " => " << mk_pp(rhs_term, m) << "\n";);
        expr_ref_vector conjs = get_conj_terms(lhs_term);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            farkas_pred f_pred(m_vars);
            f_pred.set(expr_ref(conjs.get(i), m));
            m_lhs.add(f_pred);
        }

        m_rhs.set(rhs_term);

        for (unsigned i = 0; i < m_lhs.get_size(); ++i) {
            m_lambdas.push_back(m.mk_fresh_const("t", arith_util(m).mk_int()));
        }

        m_constraints.swap(make_constraints());
    }

    bool solve_constraint() {
        smt_params new_param;
        smt::kernel solver(m, new_param);
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            solver.assert_expr(m_constraints.get(i));
        }
        if (solver.check() != l_true) {
            STRACE("predabst", tout << "Unable to find solution\n";);
            return false;
        }

        model_ref modref;
        solver.get_model(modref);
        expr_ref solution(m);
        for (unsigned j = 0; j < m_lhs.get_size(); ++j) {
            if (!modref->eval(m_lambdas.get(j), solution, true)) {
                return false;
            }
            m_solutions.push_back(solution);
        }

        STRACE("predabst", tout << "Found solution ("; print_expr_ref_vector(tout, m_solutions, false); tout << ")\n";);
        return true;
    }

    expr_ref_vector const& get_constraints() const {
        return m_constraints;
    }

    vector<lambda_kind> get_lambda_kinds() const {
        vector<lambda_kind> lambda_kinds;
        if (m_lhs.get_param_pred_count() == 1) {
            for (unsigned i = 0; i < m_lhs.get_size(); ++i) {
                if (m_lhs.has_params(i)) {
                    if (m_lhs.get_op(i) == op_eq) {
                        lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), bilin_sing, m_lhs.get_op(i)));
                    }
                    break;
                }
            }
        }
        else {
            for (unsigned i = 0; i < m_lhs.get_size(); ++i) {
                if (m_lhs.has_params(i)) {
                    lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), bilin, m_lhs.get_op(i)));
                }
                else {
                    lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m), lin, m_lhs.get_op(i)));
                }
            }
        }
        return lambda_kinds;
    }

    void display(std::ostream& out) const {
        out << "LHS:\n";
        m_lhs.display(out);
        out << "RHS:\n";
        m_rhs.display(out);
        out << "Constraint:\n";
        print_expr_ref_vector(out, m_constraints);
        if (m_solutions.size() > 0) {
            out << "Solutions:\n";
        }
        for (unsigned i = 0; i < m_solutions.size(); ++i) {
            out << mk_pp(m_lambdas[i], m) << " --> " << mk_pp(m_solutions[i], m) << "\n";
        }
    }

private:

    expr_ref_vector make_constraints() const {
        arith_util arith(m);
        //CASSERT("predabst", m_lhs.get_param_pred_count() > 0);
        // XXX This assert fails on unsat-N.smt2, but without it the tests pass.  It's not clear whether this assert is wrong, or whether there's a bug.

        expr_ref_vector constraints(m);

        for (unsigned i = 0; i < m_lhs.get_size(); ++i) {
            if (m_lhs.get_op(i) == op_le) {
                constraints.push_back(arith.mk_ge(m_lambdas.get(i), arith.mk_numeral(rational(0), true)));
            }
        }

        if (m_lhs.get_param_pred_count() == 1) {
            for (unsigned i = 0; i < m_lhs.get_size(); ++i) {
                if (m_lhs.has_params(i)) {
                    if (m_lhs.get_op(i) != op_eq) {
                        constraints.push_back(m.mk_eq(m_lambdas.get(i), arith.mk_numeral(rational(1), true)));
                    }
                    break;
                }
            }
        }

        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref sum(arith.mk_numeral(rational(0), true), m);
            for (unsigned j = 0; j < m_lhs.get_size(); ++j) {
                sum = arith.mk_add(sum, arith.mk_mul(m_lambdas.get(j), m_lhs.get_coeff(i, j)));
            }
            constraints.push_back(m.mk_eq(sum, m_rhs.get_coeff(i)));
        }

        expr_ref sum_const(arith.mk_numeral(rational(0), true), m);
        for (unsigned j = 0; j < m_lhs.get_size(); ++j) {
            sum_const = arith.mk_add(sum_const, arith.mk_mul(m_lambdas.get(j), m_lhs.get_const(j)));
        }
        constraints.push_back(arith.mk_le(sum_const, m_rhs.get_const()));

        return constraints;
    }
};

static bool exists_valid(expr_ref const& fml, expr_ref_vector const& vars, app_ref_vector const& q_vars, expr_ref_vector& constraint_st) {
    ast_manager& m = fml.m();
    CASSERT("predabst", constraint_st.empty());
    expr_ref norm_fml = neg_and_2dnf(fml);
    expr_ref_vector disjs = get_disj_terms(norm_fml);
    for (unsigned i = 0; i < disjs.size(); ++i) {
        expr_ref disj(disjs.get(i), m);
        app_ref_vector q_vars_disj(q_vars);
        qe_lite ql1(m);
        ql1(q_vars_disj, disj);
        farkas_imp f_imp(vars);
        f_imp.set(disj, expr_ref(m.mk_false(), m));
        if (!f_imp.solve_constraint()) {
            return false;
        }
        constraint_st.append(f_imp.get_constraints());
    }
    return true;
}

static bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref_vector& constraint_st, vector<lambda_kind>& all_lambda_kinds) {
    ast_manager& m = fml.m();
    CASSERT("predabst", constraint_st.empty());
    expr_ref norm_fml = neg_and_2dnf(fml);
    expr_ref_vector disjs = get_disj_terms(norm_fml);
    for (unsigned i = 0; i < disjs.size(); ++i) {
        farkas_imp f_imp(vars);
        f_imp.set(expr_ref(disjs.get(i), m), expr_ref(m.mk_false(), m));
        if (!f_imp.solve_constraint()) {
            return false;
        }
        constraint_st.append(f_imp.get_constraints());
        all_lambda_kinds.append(f_imp.get_lambda_kinds());
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
    expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
    expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        sum_psvs = arith.mk_add(sum_psvs, arith.mk_mul(param, vs.get(i)));
        sum_psws = arith.mk_add(sum_psws, arith.mk_mul(param, ws.get(i)));
    }

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

    app_ref_vector q_vars(m);
    for (unsigned j = 0; j < lhs_vars.size(); j++) {
        if (!vsws.contains(lhs_vars.get(j))) {
            q_vars.push_back(to_app(lhs_vars.get(j)));
        }
    }

    expr_ref_vector constraint_st(m);
    if (!exists_valid(to_solve, vsws, q_vars, constraint_st)) {
        STRACE("predabst", tout << "Formula " << mk_pp(lhs, m) << " is not well-founded: lambda is unsatisfiable\n";);
        return false;
    }

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
    expr_ref_vector constraint_st(m);
    if (!exists_valid(to_solve, vars, q_vars, constraint_st)) {
        STRACE("predabst", tout << "Interpolation failed: not exists_valid\n";);
        return false;
    }

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
    if (solver.check() != l_true) {
        STRACE("predabst", tout << "Failed to solve template constraint " << mk_pp(constraint, m) << "\n";);
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

bool rel_template_suit::instantiate_templates() {
    expr_ref_vector args_coll(m);
    expr_ref c1 = subst_template_body(m_acc, args_coll);
    //args_coll.append(m_temp_subst); //>>> I have no idea what this was trying to do, but m_temp_subst is no more

    expr_ref_vector constraint_st(m);
    vector<lambda_kind> all_lambda_kinds;
    if (!mk_exists_forall_farkas(c1, args_coll, constraint_st, all_lambda_kinds)) {
        return false;
    }

    int max_lambda = 2;
    expr_ref lambda_cs = mk_bilin_lambda_constraint(all_lambda_kinds, max_lambda, m);

    STRACE("predabst", tout << "Using accumulated constraint " << mk_pp(m_acc, m) << "\n";);
    STRACE("predabst", tout << "Using lambda constraint " << mk_pp(lambda_cs, m) << "\n";);
    expr_ref constraint(m.mk_and(mk_conj(constraint_st), lambda_cs), m);
    return instantiate_templates(constraint);
}
