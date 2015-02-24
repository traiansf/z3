/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_util.h

Abstract:

    Miscellaneous utilities for use by predabst.

Author:

    James Lingard (jchl) 2015-02-05.

Revision History:

--*/
#ifndef _PREDABST_UTIL_H_
#define _PREDABST_UTIL_H_

#include "ast.h"

template<typename T, typename TManager>
inline ref_vector<T, TManager> vector_concat(ref_vector<T, TManager> const& v1, ref_vector<T, TManager> const& v2) {
    ref_vector<T, TManager> v(v1);
    v.append(v2);
    return v;
}

expr_ref_vector get_conj_terms(expr_ref const& e);

expr_ref_vector get_additive_terms(expr_ref const& e);

expr_ref_vector get_multiplicative_factors(expr_ref const& e);

expr_ref mk_disj(expr_ref_vector const& terms);

expr_ref mk_conj(expr_ref_vector const& terms);

expr_ref mk_conj(expr_ref const& term1, expr_ref const& term2);

expr_ref mk_sum(expr_ref_vector const& terms);

expr_ref mk_prod(expr_ref_vector const& terms);

expr* replace_pred(expr_ref_vector const& args, expr_ref_vector const& vars, expr* e);

expr_ref_vector get_all_vars(expr_ref const& fml);

expr_ref neg_and_2dnf(expr_ref const& fml);

void print_expr_ref_vector(std::ostream& out, expr_ref_vector const& v, bool newline = true);

#endif /* _PREDABST_UTIL_H */
