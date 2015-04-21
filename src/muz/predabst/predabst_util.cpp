/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_util.cpp

Abstract:

    Miscellaneous utilities for use by predabst.

Author:

    James Lingard (jchl) 2015-02-05.

Revision History:

--*/
#include "predabst_util.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "smt_kernel.h"
#include "smt_params.h"
#include "qe_lite.h"

bool sort_is_bool(expr* e, ast_manager& m) {
    return get_sort(e) == m.mk_bool_sort();
}

bool sort_is_int(expr* e, ast_manager& m) {
    return get_sort(e) == arith_util(m).mk_int();
}

static void get_disj_terms(expr* e, ast_manager& m, expr_ref_vector& terms) {
    if (m.is_or(e)) {
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            get_disj_terms(to_app(e)->get_arg(i), m, terms);
        }
    }
    else if (m.is_false(e)) {
        // do nothing
    }
    else {
        terms.push_back(e);
    }
}

expr_ref_vector get_disj_terms(expr_ref const& e) {
    expr_ref_vector terms(e.m());
    get_disj_terms(e, e.m(), terms);
    return terms;
}

static void get_conj_terms(expr* e, ast_manager& m, expr_ref_vector& terms) {
    if (m.is_and(e)) {
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            get_conj_terms(to_app(e)->get_arg(i), m, terms);
        }
    }
    else if (m.is_true(e)) {
        // do nothing
    }
    else {
        terms.push_back(e);
    }
}

expr_ref_vector get_conj_terms(expr_ref const& e) {
    expr_ref_vector terms(e.m());
    get_conj_terms(e, e.m(), terms);
    return terms;
}

static void get_additive_terms(expr* e, ast_manager& m, expr_ref_vector& terms) {
    arith_util arith(m);
    if (arith.is_add(e)) {
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            get_additive_terms(to_app(e)->get_arg(i), m, terms);
        }
    }
    else if (arith.is_zero(e)) {
        // do nothing
    }
    else {
        terms.push_back(e);
    }
}

expr_ref_vector get_additive_terms(expr_ref const& e) {
    expr_ref_vector terms(e.m());
    get_additive_terms(e, e.m(), terms);
    return terms;
}

static void get_multiplicative_factors(expr* e, ast_manager& m, expr_ref_vector& factors) {
    arith_util arith(m);
    if (arith.is_mul(e)) {
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            get_multiplicative_factors(to_app(e)->get_arg(i), m, factors);
        }
    }
    else if (arith.is_one(e)) {
        // do nothing
    }
    else {
        factors.push_back(e);
    }
}

expr_ref_vector get_multiplicative_factors(expr_ref const& e) {
    expr_ref_vector factors(e.m());
    get_multiplicative_factors(e, e.m(), factors);
    return factors;
}

expr_ref mk_not(expr_ref const& term) {
    ast_manager& m = term.m();
    CASSERT("predabst", sort_is_bool(term, m));
    if (m.is_true(term)) {
		return expr_ref(m.mk_false(), m);
	}
	else if (m.is_false(term)) {
		return expr_ref(m.mk_true(), m);
	}
    else if (m.is_not(term)) {
        return expr_ref(to_app(term)->get_arg(0), m);
    }
    else {
        return expr_ref(m.mk_not(term), m);
    }
}

expr_ref mk_disj(expr_ref_vector const& terms) {
    ast_manager& m = terms.m();
    for (unsigned i = 0; i < terms.size(); ++i) {
        CASSERT("predabst", sort_is_bool(terms[i], m));
    }
    if (terms.size() == 0) {
        return expr_ref(m.mk_false(), m);
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), m);
    }
    else {
        return expr_ref(m.mk_or(terms.size(), terms.c_ptr()), m);
    }
}

expr_ref mk_conj(expr_ref_vector const& terms) {
    ast_manager& m = terms.m();
    for (unsigned i = 0; i < terms.size(); ++i) {
        CASSERT("predabst", sort_is_bool(terms[i], m));
    }
    if (terms.size() == 0) {
        return expr_ref(m.mk_true(), m);
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), m);
    }
    else {
        return expr_ref(m.mk_and(terms.size(), terms.c_ptr()), m);
    }
}

expr_ref mk_sum(expr_ref_vector const& terms) {
    ast_manager& m = terms.m();
    arith_util arith(m);
    for (unsigned i = 0; i < terms.size(); ++i) {
        CASSERT("predabst", sort_is_int(terms[i], m));
    }
    if (terms.size() == 0) {
        return expr_ref(arith.mk_numeral(rational::zero(), true), m);
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), m);
    }
    else {
        return expr_ref(arith.mk_add(terms.size(), terms.c_ptr()), m);
    }
}

expr_ref mk_prod(expr_ref_vector const& terms) {
    ast_manager& m = terms.m();
    arith_util arith(m);
    for (unsigned i = 0; i < terms.size(); ++i) {
        CASSERT("predabst", sort_is_int(terms[i], m));
    }
    if (terms.size() == 0) {
        return expr_ref(arith.mk_numeral(rational::one(), true), m);
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), m);
    }
    else {
        return expr_ref(arith.mk_mul(terms.size(), terms.c_ptr()), m);
    }
}

expr* replace_pred(expr_ref_vector const& args, var_ref_vector const& vars, expr* e) {
    ast_manager& m = args.m();
    arith_util arith(m);
    CASSERT("predabst", args.size() == vars.size());
    CASSERT("predabst", is_app(e));
    if (to_app(e)->get_num_args() == 0) {
        for (unsigned i = 0; i < args.size(); ++i) {
            if (args.get(i) == e) {
                return vars.get(i);
            }
        }
        return e;
    }
    else {
        expr_ref_vector es(m);
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            es.push_back(replace_pred(args, vars, to_app(e)->get_arg(i)));
        }
        return m.mk_app(to_app(e)->get_decl(), es.size(), es.c_ptr());
    }
}

expr_ref_vector get_all_vars(expr_ref const& fml) {
    ast_manager& m = fml.m();
    arith_util arith(m);
    expr_ref_vector vars(m);
    expr_ref_vector todo(m);
    todo.push_back(fml);
    while (!todo.empty()) {
        expr* e = todo.back();
        todo.pop_back();
        CASSERT("predabst", is_app(e));
        if (is_uninterp_const(e)) {
            if (!vars.contains(e)) {
                vars.push_back(e);
            }
        }
        else {
            todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
        }
    }
    return vars;
}

void quantifier_elimination(expr_ref_vector const& vars, expr_ref& fml) {
    ast_manager& m = fml.get_manager();
    app_ref_vector q_vars(m);
    expr_ref_vector all_vars = get_all_vars(fml);
    for (unsigned j = 0; j < all_vars.size(); j++) {
        if (!vars.contains(all_vars.get(j))) {
            q_vars.push_back(to_app(all_vars.get(j)));
        }
    }
    STRACE("predabst", tout << "Eliminating existentials " << q_vars << " from " << mk_pp(fml, m) << " in variables " << vars << " ...\n";);
    qe_lite ql(m);
    ql(q_vars, fml);
    STRACE("predabst", tout << "... produces " << mk_pp(fml, m) << "\n";);
}

static expr_ref negate_expr(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    arith_util a(m);

    expr_ref new_formula(m);
    expr *e1, *e2;
    if (m.is_eq(fml, e1, e2) && sort_is_int(e1, m)) {
        CASSERT("predabst", sort_is_int(e2, m));
        new_formula = m.mk_or(a.mk_lt(e1, e2), a.mk_gt(e1, e2));
    }
    else if (a.is_lt(fml, e1, e2)) {
        new_formula = a.mk_ge(e1, e2);
    }
    else if (a.is_le(fml, e1, e2)) {
        new_formula = a.mk_gt(e1, e2);
    }
    else if (a.is_gt(fml, e1, e2)) {
        new_formula = a.mk_le(e1, e2);
    }
    else if (a.is_ge(fml, e1, e2)) {
        new_formula = a.mk_lt(e1, e2);
    }
    else {
        new_formula = mk_not(fml);
    }
    return new_formula;
}

static expr_ref negate_and_to_nnf(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    if (m.is_and(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(negate_and_to_nnf(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_disj(new_sub_formulas);
    }
    else if (m.is_or(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(negate_and_to_nnf(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_conj(new_sub_formulas);
    }
    else if (m.is_not(fml)) {
        return to_nnf(expr_ref(to_app(fml)->get_arg(0), m));
    }
    else {
        return negate_expr(fml);
    }
}

expr_ref to_nnf(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    if (m.is_and(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(to_nnf(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_conj(new_sub_formulas);
    }
    else if (m.is_or(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(to_nnf(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_disj(new_sub_formulas);
    }
    else if (m.is_not(fml)) {
        return negate_and_to_nnf(expr_ref(to_app(fml)->get_arg(0), m));
    }
    else {
        return fml;
    }
}

static vector<expr_ref_vector> to_dnf_struct(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    vector<expr_ref_vector> dnf_struct;
    if (m.is_and(fml)) {
        // Return the Cartesian product of the DNF structures corresponding
        // to the child nodes.
        dnf_struct.push_back(expr_ref_vector(m));
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            vector<expr_ref_vector> next = to_dnf_struct(expr_ref(to_app(fml)->get_arg(i), m));
            // Replicate dnf_struct next.size() times.
            if (next.size() == 0) {
                dnf_struct.reset();
                break;
            }
            unsigned old_size = dnf_struct.size();
            for (unsigned j = 1; j < next.size(); ++j) {
                for (unsigned k = 0; k < old_size; ++k) {
                    dnf_struct.push_back(dnf_struct[k]);
                }
            }
            // Extend each element of dnf_struct with one element of next.
            for (unsigned j = 0; j < next.size(); ++j) {
                for (unsigned k = 0; k < old_size; ++k) {
                    dnf_struct[(j * old_size) + k].append(next[j]);
                }
            }
        }
    }
    else if (m.is_or(fml)) {
        // Return the union of the DNF structures corresponding to the child
        // nodes.
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            dnf_struct.append(to_dnf_struct(expr_ref(to_app(fml)->get_arg(i), m)));
        }
    }
    else if (m.is_true(fml)) {
        // true is represented by (OR (AND <empty>)).
        dnf_struct.push_back(expr_ref_vector(m));
    }
    else if (m.is_false(fml)) {
        // false is represented by (OR <empty>).
    }
    else {
        CASSERT("predabst", sort_is_bool(fml, m));
        expr_ref_vector tmp(m);
        tmp.push_back(fml);
        dnf_struct.push_back(tmp);
    }
    return dnf_struct;
}

expr_ref to_dnf(expr_ref const& fml) {
    vector<expr_ref_vector> dnf_struct = to_dnf_struct(to_nnf(fml));
    expr_ref_vector disjs(fml.m());
    for (unsigned i = 0; i < dnf_struct.size(); ++i) {
        disjs.push_back(mk_conj(dnf_struct[i]));
    }
    return mk_disj(disjs);
}
