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

template<typename T, typename TManager>
inline unsigned vector_find(ref_vector<T, TManager> const& v, T const* elem) {
    for (unsigned i = 0; i < v.size(); ++i) {
        if (v.get(i) == elem) {
            return i;
        }
    }
    UNREACHABLE();
    return UINT_MAX;
}

template<typename T, typename TManager>
std::ostream& operator<<(std::ostream& out, ref_vector<T, TManager> const& v) {
    TManager& m = v.m();
    for (unsigned i = 0; i < v.size(); ++i) {
        if (v[i]) {
            out << mk_pp(v[i], m);
        }
        else {
            out << "NULL";
        }
        if (i + 1 < v.size()) {
            out << ", ";
        }
    }
    return out;
}

expr_ref_vector get_disj_terms(expr_ref const& e);

expr_ref_vector get_conj_terms(expr_ref const& e);

expr_ref_vector get_additive_terms(expr_ref const& e);

expr_ref_vector get_multiplicative_factors(expr_ref const& e);

expr_ref mk_not(expr_ref const& term);

expr_ref mk_disj(expr_ref_vector const& terms);

expr_ref mk_conj(expr_ref_vector const& terms);

expr_ref mk_conj(expr_ref const& term1, expr_ref const& term2);

expr_ref mk_sum(expr_ref_vector const& terms);

expr_ref mk_prod(expr_ref_vector const& terms);

expr* replace_pred(expr_ref_vector const& args, expr_ref_vector const& vars, expr* e);

expr_ref_vector get_all_vars(expr_ref const& fml);

void quantifier_elimination(expr_ref_vector const& vars, expr_ref& fml);

expr_ref to_nnf(expr_ref const& fml);

expr_ref to_dnf(expr_ref const& fml);

#endif /* _PREDABST_UTIL_H */
