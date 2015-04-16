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

expr_ref make_linear_combination(vector<unsigned> const& coeffs, expr_ref_vector const& inequalities);

bool mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, expr_ref_vector& constraints, vector<lambda_info>& lambda_infos, bool eliminate_unsat_disjuncts = false);

void well_founded_bound_and_decrease(expr_ref_vector const& vsws, expr_ref& bound, expr_ref& decrease);

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref* sol_bound, expr_ref* sol_decrease);

expr_ref_vector mk_bilinear_lambda_constraints(vector<lambda_info> const& lambda_infos, int max_lambda, ast_manager& m);

#endif /* _FARKAS_UTIL_H_ */
