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
#ifndef _FARKAS_UTIL_H_
#define _FARKAS_UTIL_H_

#include "ast.h"

typedef enum { linear, bilinear, bilinear_single } lambda_kind;
typedef enum { op_eq, op_le } rel_op;

std::ostream& operator<<(std::ostream& ostr, rel_op op);

class linear_inequality {
	// Represents a linear integer (in)equality in m_nvars variables.
	//
	// Specifically, represents the (in)equality:
	//     (Sigma_i (xi * m_coeffs[i])) m_op m_const
	// where the xi are distinct variables, and m_coeffs and
	// m_const do not contain any of those variables.

	unsigned const m_nvars;
	expr_ref_vector m_coeffs;
	rel_op m_op;
	expr_ref m_const;

	bool m_has_params; // true if m_coeffs or m_const contain any uninterpreted constants

	ast_manager& m;

public:
	// Initializes this object to represent the inequality 0 <= -1
	// (i.e. false).
	linear_inequality(unsigned nvars, ast_manager& m);

	linear_inequality& operator=(linear_inequality const& other);

	// Initializes this object from an expression representing a (binary)
	// linear integer (in)equality.  Returns false if this is impossible,
	// i.e. if the expression is not a (binary) (in)equality, if the
	// operands are not integers, or if they are not linear in m_vars.
	bool set_from_expr(expr_ref const& e, expr_ref_vector const& vars);

	// Initializes this object from a linear combination of linear
	// (in)equalities in the same variables.
	void set_from_linear_combination(vector<int64> const& coeffs, vector<linear_inequality> const& inequalities);

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

	expr_ref to_expr(expr_ref_vector const& vars) const;

	friend std::ostream& operator<<(std::ostream& out, linear_inequality const& lineq);
	friend class farkas_imp;
	friend void get_farkas_coeffs(vector<linear_inequality> const& inequalities, vector<int64>& coeffs);
};

struct lambda_info {
	expr_ref const m_lambda;
	lambda_kind const m_kind;
	rel_op const m_op;

	lambda_info(expr_ref const& lambda, lambda_kind kind, rel_op op) :
		m_lambda(lambda),
		m_kind(kind),
		m_op(op) {
	}
};

bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref_vector& constraints, vector<lambda_info>& lambda_infos, bool eliminate_unsat_disjuncts = false);

void get_farkas_coeffs(vector<linear_inequality> const& inequalities, vector<int64>& coeffs);

void well_founded_bound_and_decrease(expr_ref_vector const& vsws, expr_ref& bound, expr_ref& decrease);

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref* sol_bound, expr_ref* sol_decrease);

expr_ref_vector mk_bilinear_lambda_constraints(vector<lambda_info> const& lambda_infos, int max_lambda, ast_manager& m);

expr_ref normalize_pred(expr_ref const& e, var_ref_vector const& vars);

#endif /* _FARKAS_UTIL_H_ */
