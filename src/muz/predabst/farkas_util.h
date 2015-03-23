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

typedef enum { bilin_sing, bilin } lambda_kind_sort;
typedef enum { op_eq, op_le } rel_op;

std::ostream& operator<<(std::ostream& ostr, rel_op op);

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

expr_ref_vector mk_exists_forall_farkas(expr_ref const& fml, expr_ref_vector const& vars, vector<lambda_kind>& lambda_kinds, bool eliminate_unsat_disjuncts = false);

bool interpolate(expr_ref_vector const& vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol);

void well_founded_bound_and_decrease(expr_ref_vector const& vsws, expr_ref& bound, expr_ref& decrease);

bool well_founded(expr_ref_vector const& vsws, expr_ref const& lhs, expr_ref* sol_bound, expr_ref* sol_decrease);

expr_ref_vector mk_bilin_lambda_constraints(vector<lambda_kind> const& lambda_kinds, int max_lambda, ast_manager& m);

#endif /* _FARKAS_UTIL_H_ */
