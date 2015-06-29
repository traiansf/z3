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

// Returns the number of lambdas of kind 'bilinear' or 'bilinear_single'
// that are still uninterpreted constants (i.e. which haven't been
// substituted for a specific value).
static unsigned count_bilinear_uninterp_const(vector<lambda_info> const& lambdas) {
    unsigned num_bilinear_uninterp_const = 0;
    for (unsigned i = 0; i < lambdas.size(); i++) {
        if (((lambdas[i].m_kind == bilinear) || (lambdas[i].m_kind == bilinear_single)) &&
            is_uninterp_const(lambdas[i].m_lambda)) {
            ++num_bilinear_uninterp_const;
        }
    }
    return num_bilinear_uninterp_const;
}

// Converts an integer (in)equality (E1 op E2) to the form (E' op' 0),
// where op' is either = or <=.  Returns false if the expression is not a
// binary integer (in)equality.
static bool leftify_inequality(expr_ref const& e, expr_ref& new_e, rel_op& new_op) {
    ast_manager& m = e.m();
    arith_util arith(m);
    CASSERT("predabst", is_well_sorted(m, e));

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
        STRACE("predabst", tout << "Expression is not a binary (in)equality: " << e << "\n";);
        return false;
    }

    if (!sort_is_int(e1, m)) {
        STRACE("predabst", tout << "Operands of (in)equality are not integers: " << e << "\n";);
        return false;
    }

    CASSERT("predabst", sort_is_int(e2, m));
    CASSERT("predabst", is_well_sorted(m, new_e));
    CASSERT("predabst", sort_is_int(new_e, m));
    return true;
}

linear_inequality::linear_inequality(unsigned nvars, ast_manager& m) :
	m_nvars(nvars),
	m_coeffs(m),
	m_op(op_le),
	m_const(m),
	m_has_params(false),
	m(m) {
	for (unsigned i = 0; i < nvars; ++i) {
		m_coeffs.push_back(arith_util(m).mk_numeral(rational::zero(), true));
	}
	m_const = arith_util(m).mk_numeral(rational::minus_one(), true);
}

linear_inequality& linear_inequality::operator=(linear_inequality const& other) {
	CASSERT("predabst", m_nvars == other.m_nvars);
	m_coeffs.reset();
	m_coeffs.append(other.m_coeffs);
	m_op = other.m_op;
	m_const = other.m_const;
	m_has_params = other.m_has_params;
	return *this;
}

bool linear_inequality::set_from_expr(expr_ref const& e, expr_ref_vector const& vars) {
	CASSERT("predabst", vars.size() == m_nvars);
	CASSERT("predabst", is_well_sorted(m, e));
	arith_util arith(m);
	th_rewriter rw(m);

	for (unsigned i = 0; i < vars.size(); ++i) {
		expr_ref var(vars.get(i), m);
		CASSERT("predabst", is_var(var) || is_uninterp_const(var));
		if (!sort_is_int(var, m)) {
			STRACE("predabst", tout << "Found non-integer variable " << var << "\n";);
			return false;
		}
	}

	m_coeffs.reset();
	m_has_params = false;

	// Push all terms to the LHS of the (in)equality.
	expr_ref lhs(m);
	bool result = leftify_inequality(e, lhs, m_op);
	if (!result) {
		return false;
	}

	// Simplify the LHS of the (in)equality.  The simplified expression
	// will be a sum of terms, each of which is a product of factors.
	rw(lhs);

	// Split the terms into those which have one of the vars as a
	// factor (var_terms), and those which do not (const_terms), while
	// checking that all the terms are linear in vars.
	vector<expr_ref_vector> var_terms;
	var_terms.reserve(m_nvars, expr_ref_vector(m));
	expr_ref_vector const_terms(m);

	expr_ref_vector terms = get_additive_terms(lhs);
	for (unsigned i = 0; i < terms.size(); ++i) {
		expr_ref term(terms.get(i), m);

		// Split the factors into those which are one of the vars
		// (var_factors) and those which are not (const_factors).
		expr_ref_vector var_factors(m);
		expr_ref_vector const_factors(m);

		expr_ref_vector factors = get_multiplicative_factors(term);
		for (unsigned j = 0; j < factors.size(); ++j) {
			expr_ref factor(factors.get(j), m);
			if (vars.contains(factor)) {
				var_factors.push_back(factor);
			}
			else {
				expr_ref_vector factor_vars = get_all_vars(factor);
				for (unsigned k = 0; k < factor_vars.size(); ++k) {
					if (vars.contains(factor_vars.get(k))) {
						STRACE("predabst", tout << "Found non-linear factor " << factor << "\n";);
						return false;
					}
				}
				const_factors.push_back(factor);
			}
		}

		// Classify the term based on the number of var_factors it
		// contains.
		if (var_factors.size() == 0) {
			const_terms.push_back(term);
		}
		else if (var_factors.size() == 1) {
			unsigned j = vector_find(vars, var_factors.get(0));
			var_terms[j].push_back(mk_prod(const_factors));
		}
		else {
			STRACE("predabst", tout << "Found non-linear term " << term << "\n";);
			return false;
		}
	}

	for (unsigned i = 0; i < m_nvars; ++i) {
		expr_ref coeff(mk_sum(var_terms.get(i)), m);
		rw(coeff);
		m_coeffs.push_back(coeff);
		if (!arith.is_numeral(coeff)) {
			m_has_params = true;
		}
	}
	// Move the constant terms to the RHS of the (in)equality.
	m_const = arith.mk_uminus(mk_sum(const_terms));
	rw(m_const);
	if (!arith.is_numeral(m_const)) {
		m_has_params = true;
	}

	return true;
}

void linear_inequality::set_from_linear_combination(vector<int64> const& coeffs, vector<linear_inequality> const& inequalities) {
	CASSERT("predabst", coeffs.size() == inequalities.size());
	arith_util arith(m);
	th_rewriter rw(m);

	m_coeffs.reset();
	m_op = op_eq;
	m_has_params = false;

	vector<expr_ref_vector> var_terms;
	var_terms.reserve(m_nvars, expr_ref_vector(m));
	expr_ref_vector const_terms(m);

	for (unsigned i = 0; i < inequalities.size(); ++i) {
		expr_ref coeff(arith.mk_numeral(rational(coeffs[i], rational::i64()), true), m);
		linear_inequality const& lineq = inequalities[i];
		CASSERT("predabst", lineq.m_nvars == m_nvars);
		for (unsigned j = 0; j < m_nvars; ++j) {
			var_terms[j].push_back(arith.mk_mul(coeff, lineq.m_coeffs[j]));
		}
		const_terms.push_back(arith.mk_mul(coeff, lineq.m_const));
		CASSERT("predabst", (lineq.m_op == op_eq) || (lineq.m_op == op_le));
		if ((coeffs[i] != 0) && lineq.m_op == op_le) {
			m_op = op_le;
		}
	}

	for (unsigned i = 0; i < m_nvars; ++i) {
		expr_ref coeff(mk_sum(var_terms.get(i)), m);
		rw(coeff);
		m_coeffs.push_back(coeff);
		if (!arith.is_numeral(coeff)) {
			m_has_params = true;
		}
	}
	m_const = mk_sum(const_terms);
	rw(m_const);
	if (!arith.is_numeral(m_const)) {
		m_has_params = true;
	}
}

expr_ref linear_inequality::to_expr(expr_ref_vector const& vars) const {
	CASSERT("predabst", vars.size() == m_nvars);
	arith_util arith(m);
	expr_ref_vector lhs_terms(m);
	expr_ref_vector rhs_terms(m);

	for (unsigned i = 0; i < m_nvars; ++i) {
		expr* coeff = m_coeffs.get(i);
		rational val;
		bool is_int;
		bool result = arith.is_numeral(coeff, val, is_int);
		CASSERT("predabst", result);
		CASSERT("predabst", is_int);
		if (val.is_pos()) {
			if (val.is_one()) {
				lhs_terms.push_back(vars.get(i));
			}
			else {
				lhs_terms.push_back(arith.mk_mul(coeff, vars.get(i)));
			}
		}
		else if (val.is_neg()) {
			if (val.is_minus_one()) {
				rhs_terms.push_back(vars.get(i));
			}
			else {
				expr_ref neg_coeff(arith.mk_numeral(-val, is_int), m);
				rhs_terms.push_back(arith.mk_mul(neg_coeff, vars.get(i)));
			}
		}
		else {
			CASSERT("predabst", val.is_zero());
		}
	}

	// Prefer X + Y >= Z to Z <= X + Y, but prefer X + Y <= Z + W to Z + W >= X + Y.
	bool swap = (rhs_terms.size() > lhs_terms.size());
	bool strict = false;

	rational val;
	bool is_int;
	bool result = arith.is_numeral(m_const, val, is_int);
	CASSERT("predabst", result);
	CASSERT("predabst", is_int);
	if (val.is_pos()) {
		rhs_terms.push_back(m_const);
	}
	else if (val.is_neg()) {
		if ((m_op == op_le) && val.is_minus_one()) {
			// Prefer X < Y to X + 1 <= Y.
			strict = true;
		}
		else {
			expr_ref neg_const(arith.mk_numeral(-val, is_int), m);
			lhs_terms.push_back(neg_const);
		}
	}
	else {
		CASSERT("predabst", val.is_zero());
	}

	// Prefer X + Y + C <= Z + W to Z + W <= X + Y + C.
	swap |= (rhs_terms.size() > lhs_terms.size());

	expr_ref lhs = mk_sum(lhs_terms);
	expr_ref rhs = mk_sum(rhs_terms);
	return expr_ref(m_op == op_eq ? (swap ? m.mk_eq(rhs, lhs) : m.mk_eq(lhs, rhs)) :
		strict ? (swap ? arith.mk_gt(rhs, lhs) : arith.mk_lt(lhs, rhs)) :
		(swap ? arith.mk_ge(rhs, lhs) : arith.mk_le(lhs, rhs)), m);
}

std::ostream& operator<<(std::ostream& out, linear_inequality const& lineq) {
    ast_manager& m = lineq.m;
	arith_util arith(m);
    for (unsigned i = 0; i < lineq.m_nvars; ++i) {
        if (i != 0) {
            out << " + ";
        }
        out << expr_ref(lineq.m_coeffs[i], m) << " * x" << i;
    }
    out << " " << lineq.m_op << " " << lineq.m_const;
    if (lineq.m_has_params) {
        out << " (has params)";
    }
    return out;
}

class farkas_imp {
    // Represents an implication from a set of linear (in)equalities to
    // another linear inequality, where all the (in)equalities are linear
    // in a common set of variables.
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

    unsigned const m_nvars;
    vector<linear_inequality> m_lhs;
    linear_inequality m_rhs;
    expr_ref_vector m_lambdas;
    unsigned m_num_bilinear;

    ast_manager& m;

public:
    farkas_imp(unsigned nvars, ast_manager& m) :
        m_nvars(nvars),
        m_rhs(nvars, m),
        m_lambdas(m),
        m(m) {
    }

    // Initializes this object from a set of LHS (in)equalities and one RHS
    // inequality.  Returns false if the RHS is an equality, not an inequality.
    bool set(vector<linear_inequality> const& lhs, linear_inequality const& rhs) {
		for (unsigned i = 0; i < lhs.size(); ++i) {
			CASSERT("predabst", lhs[i].m_nvars == m_nvars);
		}
		CASSERT("predabst", rhs.m_nvars == m_nvars);
		STRACE("predabst-farkas", tout << "Solving " << lhs << " => " << rhs << ", in " << m_nvars << " variables\n";);
		m_lhs = lhs;
		m_rhs = rhs;

        if (m_rhs.get_op() == op_eq) {
            STRACE("predabst", tout << "RHS is an equality not an inequality\n";);
            return false;
        }

        m_lambdas.swap(make_lambdas(m_num_bilinear));
        return true;
    }

    // Returns a collection of constraints whose simultaneous satisfiability
    // is equivalent to the validity of the implication represented by this
    // object.  A solution to these constraints will assign a value to each
    // of the multipliers (returned by get_lambdas() (below)) that will enable
    // the RHS inequality to be derived from the LHS (in)equalities.
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
        for (unsigned i = 0; i < m_nvars; ++i) {
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

    // Returns a list of objects, in 1-to-1 correspondance with the LHS
    // (in)equalities, that describe the multipliers of those (in)equalities
    // used to derive the RHS inequality.
    vector<lambda_info> get_lambdas() const {
        vector<lambda_info> lambdas;
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            lambda_kind kind = m_lhs.get(i).has_params() ? (m_num_bilinear == 1 ? bilinear_single : bilinear) : linear;
            lambdas.push_back(lambda_info(expr_ref(m_lambdas.get(i), m), kind, m_lhs.get(i).get_op()));
        }
        return lambdas;
    }

    void display(std::ostream& out) const {
        out << "LHS:\n";
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            out << "  " << expr_ref(m_lambdas.get(i), m) << ": " << m_lhs.get(i) << std::endl;
        }
        out << "RHS:\n";
        out << "  " << m_rhs << std::endl;
    }

private:
    expr_ref_vector make_lambdas(unsigned& num_bilinear) const {
        // We classify the (in)equalities on the LHS as either 'linear' or
        // 'bilinear', according to whether the coefficients are all
        // integers, or whether some of the coefficients are uninterpreted
        // constants.
        num_bilinear = 0;
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            if (m_lhs.get(i).has_params()) {
                ++num_bilinear;
            }
        }

        expr_ref_vector lambdas(m);
        for (unsigned i = 0; i < m_lhs.size(); ++i) {
            if ((num_bilinear == 1) && m_lhs.get(i).has_params() && (m_lhs.get(i).get_op() == op_le)) {
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

// Converts a formula (Forall v, F) to an equivalent formula
// (Exists lambda, F'), where F is a formula in variables (v, p) and
// F' is a formula in variable (lambda, p), and:
//   Forall p, ((Forall v, F) <=> (Exists lambda, F'))
// In particular:
//   (Exists p, Forall v, F) <=> (Exists p, Exists lambda, F')
// the right hand side of which is of a suitable form to be answered by
// an SMT solver.
//
// The implementation uses Farkas's lemma; therefore it will fail (returning
// false) if the atomic boolean formulae in F are not all linear integer
// (in)equalities.
bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref_vector& constraints, vector<lambda_info>& lambdas, bool eliminate_unsat_disjuncts) {
    ast_manager& m = fml.m();
    arith_util arith(m);
    CASSERT("predabst", is_well_sorted(m, fml));
    CASSERT("predabst", sort_is_bool(fml, m));
    CASSERT("predabst", is_ground(fml));
    CASSERT("predabst", constraints.empty());
    CASSERT("predabst", lambdas.empty());
    for (unsigned i = 0; i < vars.size(); ++i) {
        CASSERT("predabst", is_uninterp_const(vars.get(i)));
        if (!sort_is_int(vars.get(i), m)) {
            STRACE("predabst", tout << "Cannot apply Farkas's lemma: variable " << i << " is of non-integer type\n";);
            return false;
        }
    }
    linear_inequality false_ineq(vars.size(), m);
    // P <=> (not P => false)
    expr_ref norm_fml = to_dnf(expr_ref(m.mk_not(fml), m));
    // ((P1 or ... or Pn) => false) <=> (P1 => false) and ... and (Pn => false)
    expr_ref_vector disjs = get_disj_terms(norm_fml);
    for (unsigned i = 0; i < disjs.size(); ++i) {
        expr_ref_vector conjs = get_conj_terms(expr_ref(disjs.get(i), m));
        if (eliminate_unsat_disjuncts) {
            smt_params new_param;
            new_param.m_model = false;
            smt::kernel solver(fml.m(), new_param);
            for (unsigned j = 0; j < conjs.size(); ++j) {
                solver.assert_expr(conjs.get(j));
            }
            if (solver.check() != l_true) {
                continue;
            }
        }
		vector<linear_inequality> inequalities;
		for (unsigned j = 0; j < conjs.size(); ++j) {
			inequalities.push_back(linear_inequality(vars.size(), m));
			if (!inequalities[j].set_from_expr(expr_ref(conjs.get(j), m), vars)) {
				return false;
			}
		}
        farkas_imp f_imp(vars.size(), m);
        bool result = f_imp.set(inequalities, false_ineq);
		CASSERT("predabst", result); // since f_imp.set can only fail if the RHS is an equality
        STRACE("predabst-farkas", f_imp.display(tout););
        constraints.append(f_imp.get_constraints());
        lambdas.append(f_imp.get_lambdas());
    }
    return true;
}

void get_farkas_coeffs(vector<linear_inequality> const& inequalities, vector<int64>& coeffs) {
	CASSERT("predabst", coeffs.empty());
	CASSERT("predabst", !inequalities.empty());
	ast_manager& m = inequalities[0].m;
    arith_util arith(m);
	unsigned nvars = inequalities[0].m_nvars;
    farkas_imp f_imp(nvars, m);
	linear_inequality false_ineq(nvars, m);
    bool result = f_imp.set(inequalities, false_ineq);
	CASSERT("predabst", result); // since f_imp.set can only fail if the RHS is an equality
    STRACE("predabst-farkas", f_imp.display(tout););
    smt_params new_param;
    smt::kernel solver(m, new_param);
    expr_ref_vector constraints = f_imp.get_constraints();
    for (unsigned i = 0; i < constraints.size(); ++i) {
        solver.assert_expr(constraints.get(i));
    }
    lbool lresult = solver.check();
    CASSERT("predabst", lresult == l_true);
    model_ref modref;
    solver.get_model(modref);
    CASSERT("predabst", modref);
    vector<lambda_info> lambdas = f_imp.get_lambdas();
    CASSERT("predabst", lambdas.size() == inequalities.size());
    for (unsigned i = 0; i < lambdas.size(); ++i) {
        expr_ref e(m);
        bool result = modref->eval(lambdas.get(i).m_lambda, e);
        CASSERT("predabst", result);
        rational coeff;
        bool is_int;
        result = arith.is_numeral(e, coeff, is_int);
        CASSERT("predabst", result);
        CASSERT("predabst", is_int);
        coeffs.push_back(coeff.get_int64());
    }
}

void well_founded_bound_and_decrease(expr_ref_vector const& vsws, expr_ref& bound, expr_ref& decrease) {
    ast_manager& m = vsws.get_manager();
    arith_util arith(m);
    CASSERT("predabst", vsws.size() % 2 == 0);

    expr_ref_vector vs(m);
    for (unsigned i = 0; i < (vsws.size() / 2); i++) {
        vs.push_back(vsws.get(i));
    }

    expr_ref_vector ws(m);
    for (unsigned i = (vsws.size() / 2); i < vsws.size(); ++i) {
        ws.push_back(vsws.get(i));
    }

    expr_ref_vector sum_psvs_terms(m);
    expr_ref_vector sum_psws_terms(m);
    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        CASSERT("predabst", sort_is_int(vs.get(i), m));
        sum_psvs_terms.push_back(arith.mk_mul(param, vs.get(i)));
        CASSERT("predabst", sort_is_int(ws.get(i), m));
        sum_psws_terms.push_back(arith.mk_mul(param, ws.get(i)));
    }
    expr_ref sum_psvs = mk_sum(sum_psvs_terms);
    expr_ref sum_psws = mk_sum(sum_psws_terms);

    expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);

    bound = arith.mk_ge(sum_psvs, delta0);
    STRACE("predabst", tout << "WF bound: " << bound << "\n";);
    CASSERT("predabst", is_well_sorted(m, bound));

    decrease = arith.mk_lt(sum_psws, sum_psvs);
    STRACE("predabst", tout << "WF decrease: " << decrease << "\n";);
    CASSERT("predabst", is_well_sorted(m, decrease));
}

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref* sol_bound, expr_ref* sol_decrease) {
    ast_manager& m = lhs.get_manager();
    CASSERT("predabst", vsws.size() % 2 == 0);
    CASSERT("predabst", sort_is_bool(lhs, m));
    CASSERT("predabst", (sol_bound && sol_decrease) || (!sol_bound && !sol_decrease));

    expr_ref bound(m);
    expr_ref decrease(m);
    well_founded_bound_and_decrease(vsws, bound, decrease);
    expr_ref to_solve(m.mk_or(m.mk_not(lhs), m.mk_and(bound, decrease)), m);

    expr_ref_vector all_vars(vsws);
    expr_ref_vector lhs_vars = get_all_vars(lhs);
    for (unsigned j = 0; j < lhs_vars.size(); j++) {
        if (!vsws.contains(lhs_vars.get(j))) {
            all_vars.push_back(lhs_vars.get(j));
        }
    }

    // XXX Does passing true for eliminate_unsat_disjuncts help in the refinement case?
    expr_ref_vector constraints(m);
    vector<lambda_info> lambdas;
    bool result = mk_exists_forall_farkas(to_solve, all_vars, constraints, lambdas);
    if (!result) {
        STRACE("predabst", tout << "Formula " << lhs << " is not (provably) well-founded: it does not comprise only linear integer (in)equalities\n";);
        // XXX We need to distinguish between this case and where we have proven that the formula is not well-founded, or else we can end up returning UNSAT incorrectly
        return false;
    }
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
        STRACE("predabst", tout << "Formula " << lhs << " is not well-founded: constraint is unsatisfiable\n";);
        return false;
    }

    if (sol_bound && sol_decrease) {
        model_ref modref;
        solver.get_model(modref);
        if (!(modref->eval(bound, *sol_bound) && modref->eval(decrease, *sol_decrease))) {
            return false;
        }

        STRACE("predabst", tout << "Formula " << lhs << " is well-founded, with bound " << *sol_bound << "; decrease " << *sol_decrease << "\n";);
    }
    else {
        STRACE("predabst", tout << "Formula " << lhs << " is well-founded\n";);
    }
    
    return true;
}

expr_ref_vector mk_bilinear_lambda_constraints(vector<lambda_info> const& lambdas, int max_lambda, ast_manager& m) {
    arith_util arith(m);

    expr_ref one(arith.mk_numeral(rational::one(), true), m);
    expr_ref minus_one(arith.mk_numeral(rational::minus_one(), true), m);

    expr_ref_vector constraints(m);
    for (unsigned i = 0; i < lambdas.size(); i++) {
        if (lambdas[i].m_kind == bilinear_single) {
            if (lambdas[i].m_op == op_eq) {
                // This is the sole bilinear (in)equality, and it is an
                // equality, so without loss of generality we may choose
                // its multiplier to be either 1 or -1.
                CASSERT("predabst", is_uninterp_const(lambdas[i].m_lambda));
                constraints.push_back(m.mk_or(m.mk_eq(lambdas[i].m_lambda, minus_one), m.mk_eq(lambdas[i].m_lambda, one)));
            }
            else {
                // This is the sole bilinear (in)equality, and it is an
                // inequality, so the multiplier will have been set to 1
                // above and therefore no constraint is necessary.
                CASSERT("predabst", arith.is_one(lambdas[i].m_lambda));
            }
        }
        else if (lambdas[i].m_kind == bilinear) {
            // There is more than one bilinear (in)equality.  In order to
            // make solving tractable, we assume that the multiplier is
            // between 0 and N for an inequality, or -N and N for an
            // equality.  Note that this assumption might prevent us from
            // finding a solution.
            CASSERT("predabst", is_uninterp_const(lambdas[i].m_lambda));
            int min_lambda = (lambdas[i].m_op == op_eq) ? -max_lambda : 0;
            expr_ref_vector bilin_disj_terms(m);
            for (int j = min_lambda; j <= max_lambda; j++) {
                bilin_disj_terms.push_back(m.mk_eq(lambdas[i].m_lambda, arith.mk_numeral(rational(j), true)));
            }
            constraints.push_back(mk_disj(bilin_disj_terms));
        }
    }
    return constraints;
}

expr_ref normalize_pred(expr_ref const& e, var_ref_vector const& vars) {
    ast_manager& m = e.m();
    STRACE("predabst", tout << "Normalizing: " << e << " -> ";);
    th_rewriter tw(m);
    expr_ref e2 = e;
    tw(e2); // >>> convert 0 = 0 to true, etc.
    e2 = to_nnf(e2); // >>> bit of a hack; eliminates 'not'; but also turns (not (x=y)) into a disjunction, which we probably don't want here.
    for (unsigned i = 0; i < vars.size(); ++i) {
        if (!sort_is_int(vars.get(i), m)) {
            STRACE("predabst", tout << e2 << "\n";);
            return e2;
        }
    }
    expr_ref_vector expr_vars(m, vars.size(), (expr* const*)vars.c_ptr());
    linear_inequality ineq(expr_vars.size(), m);
    if (ineq.set_from_expr(e2, expr_vars)) {
        e2 = ineq.to_expr(expr_vars);
    }
    STRACE("predabst", tout << e2 << "\n";);
    return e2;
}
