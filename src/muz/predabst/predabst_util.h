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

template<typename V>
inline bool vector_equals(V const& v1, V const& v2) {
    if (v1.size() != v2.size()) {
        return false;
    }
    for (unsigned i = 0; i < v1.size(); ++i) {
        if (v1.get(i) != v2.get(i)) {
            return false;
        }
    }
    return true;
}

template<typename V>
inline V vector_concat(V const& v1, V const& v2) {
    V v(v1);
    v.append(v2);
    return v;
}

template<typename V, typename T>
inline V vector_concat(unsigned n1, T* const* p1, V const& v2) {
    V v(v2.m(), n1, p1);
    v.append(v2);
    return v;
}

template<typename V, typename T>
inline unsigned vector_find(V const& v, T const* elem) {
    for (unsigned i = 0; i < v.size(); ++i) {
        if (v.get(i) == elem) {
            return i;
        }
    }
    UNREACHABLE();
    return UINT_MAX;
}

template<typename V>
inline V vector_intersection(V const& v1, V const& v2) {
    V intersection(v1.m());
    for (unsigned i = 0; i < v1.size(); ++i) {
        if (v2.contains(v1.get(i))) {
            intersection.push_back(v1.get(i));
        }
    }
    return intersection;
}

// Returns true if v1 is a (possibly non-strict) subset of v2.
template<typename V>
static bool vector_subset(V const& v1, V const& v2) {
	for (unsigned i = 0; i < v1.size(); ++i) {
		if (!v2.contains(v1.get(i))) {
			return false;
		}
	}
	return true;
}

template<typename T>
inline std::ostream& operator<<(std::ostream& out, vector<T> const& v) {
    for (unsigned i = 0; i < v.size(); ++i) {
        out << v[i];
        if (i + 1 < v.size()) {
            out << ", ";
        }
    }
    return out;
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

var_ref_vector to_vars(expr_ref_vector const& exprs);

bool sort_is_bool(expr* e, ast_manager& m);
bool sort_is_int(expr* e, ast_manager& m);

expr_ref_vector get_disj_terms(expr_ref const& e);
expr_ref_vector get_conj_terms(expr_ref const& e);
expr_ref_vector get_additive_terms(expr_ref const& e);
expr_ref_vector get_multiplicative_factors(expr_ref const& e);

expr_ref mk_not(expr_ref const& term);
expr_ref mk_disj(expr_ref_vector const& terms);
expr_ref mk_conj(expr_ref_vector const& terms);
expr_ref mk_sum(expr_ref_vector const& terms);
expr_ref mk_prod(expr_ref_vector const& terms);

expr* replace_pred(expr_ref_vector const& args, var_ref_vector const& vars, expr* e);

expr_ref_vector get_all_vars(expr_ref const& fml);

expr_ref_vector get_args_vector(app* a, ast_manager& m);

expr_ref_vector get_arg_fresh_consts(func_decl* fdecl, char const* prefix, ast_manager& m);
var_ref_vector get_arg_vars(func_decl* fdecl, ast_manager& m);

void quantifier_elimination(expr_ref_vector const& vars, expr_ref& fml);

expr_ref to_nnf(expr_ref const& fml);
expr_ref to_dnf(expr_ref const& fml);

#endif /* _PREDABST_UTIL_H */
