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
#include "reg_decl_plugins.h"
#include "ast_pp.h"
#include "smt_kernel.h"
#include "smt_params.h"

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
	if (term.m().is_true(term)) {
		return expr_ref(term.m().mk_false(), term.m());
	}
	else if (term.m().is_false(term)) {
		return expr_ref(term.m().mk_true(), term.m());
	}
    else {
        return expr_ref(term.m().mk_not(term), term.m());
    }
}

expr_ref mk_disj(expr_ref_vector const& terms) {
    if (terms.size() == 0) {
        return expr_ref(terms.m().mk_false(), terms.m());
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), terms.m());
    }
    else {
        return expr_ref(terms.m().mk_or(terms.size(), terms.c_ptr()), terms.m());
    }
}

expr_ref mk_conj(expr_ref_vector const& terms) {
    if (terms.size() == 0) {
        return expr_ref(terms.m().mk_true(), terms.m());
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), terms.m());
    }
    else {
        return expr_ref(terms.m().mk_and(terms.size(), terms.c_ptr()), terms.m());
    }
}

expr_ref mk_conj(expr_ref const& term1, expr_ref const& term2) {
    if (term1.m().is_true(term1)) {
        return term2;
    }
    else if (term1.m().is_true(term2)) {
        return term1;
    }
    else {
        return expr_ref(term1.m().mk_and(term1, term2), term1.m());
    }
}

expr_ref mk_sum(expr_ref_vector const& terms) {
    arith_util arith(terms.m());
    if (terms.size() == 0) {
        return expr_ref(arith.mk_numeral(rational(0), true), terms.m());
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), terms.m());
    }
    else {
        return expr_ref(arith.mk_add(terms.size(), terms.c_ptr()), terms.m());
    }
}

expr_ref mk_prod(expr_ref_vector const& terms) {
    arith_util arith(terms.m());
    if (terms.size() == 0) {
        return expr_ref(arith.mk_numeral(rational(1), true), terms.m());
    }
    else if (terms.size() == 1) {
        return expr_ref(terms.get(0), terms.m());
    }
    else {
        return expr_ref(arith.mk_mul(terms.size(), terms.c_ptr()), terms.m());
    }
}

expr* replace_pred(expr_ref_vector const& args, expr_ref_vector const& vars, expr* e) {
    ast_manager& m = args.m();
    arith_util arith(m);
    CASSERT("predabst", args.size() == vars.size());
    CASSERT("predabst", is_app(e));
    expr* e1;
    expr* e2;
    if (m.is_eq(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return m.mk_eq(ee1, ee2);
    }
    else if (arith.is_le(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return arith.mk_le(ee1, ee2);
    }
    else if (arith.is_ge(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return arith.mk_ge(ee1, ee2);
    }
    else if (arith.is_lt(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return arith.mk_lt(ee1, ee2);
    }
    else if (arith.is_gt(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return arith.mk_gt(ee1, ee2);
    }
    else if (arith.is_add(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return arith.mk_add(ee1, ee2);
    }
    else if (arith.is_mul(e, e1, e2)) {
        expr* ee1 = replace_pred(args, vars, e1);
        expr* ee2 = replace_pred(args, vars, e2);
        return arith.mk_mul(ee1, ee2);
    }
    else if (m.is_not(e, e1)) {
        expr* ee1 = replace_pred(args, vars, e1);
        return m.mk_not(ee1);
    }
    else if (to_app(e)->get_num_args() == 0) {
        for (unsigned i = 0; i < args.size(); ++i) {
            if (args.get(i) == e) {
                return vars.get(i);
            }
        }
        return e;
    }
    else {
        STRACE("predabst", tout << "Unable to recognize predicate " << mk_pp(e, m) << "\n";);
        UNREACHABLE();
        return nullptr;
    }
}

expr_ref_vector get_all_vars(expr_ref const& fml) {
    ast_manager& m = fml.m();
    arith_util arith(m);
    expr_ref_vector vars(m);
    expr_ref_vector todo(m);
    todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
    while (!todo.empty()) {
        expr* e = todo.back();
        todo.pop_back();
        CASSERT("predabst", is_app(e));
        if (to_app(e)->get_num_args() == 0) {
            if (!arith.is_numeral(e) && !vars.contains(e)) {
                vars.push_back(e);
            }
        }
        else {
            todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
        }
    }
    return vars;
}

template<typename T, typename TManager>
static ref_vector<T, TManager> vector_union(ref_vector<T, TManager> const& v1, ref_vector<T, TManager> const& v2) {
    ref_vector<T, TManager> result(v1);
    result.append(v2);
    return result;
}

static vector<expr_ref_vector> cnf_to_dnf_struct(vector<vector<expr_ref_vector> > const& cnf_sets) {
    vector<expr_ref_vector> sofar;
    sofar.push_back(expr_ref_vector(m));
    for (unsigned k = 0; k < cnf_sets.size(); ++k) {
        vector<expr_ref_vector> tmp;
        vector<expr_ref_vector> const& next = cnf_sets.get(k);
        for (unsigned i = 0; i < sofar.size(); ++i) {
            for (unsigned j = 0; j < next.size(); ++j) {
                tmp.push_back(vector_union(sofar[i], next[j]));
            }
        }
        sofar = tmp;
    }
    return sofar;
}

static vector<expr_ref_vector> to_dnf_struct(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    if (m.is_and(fml)) {
        vector<vector<expr_ref_vector> > dnf_sub_structs;
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            dnf_sub_structs.push_back(to_dnf_struct(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return cnf_to_dnf_struct(dnf_sub_structs);
    }
    else {
        vector<expr_ref_vector> dnf_struct;
        if (m.is_or(fml)) {
            for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
                dnf_struct.append(to_dnf_struct(expr_ref(to_app(fml)->get_arg(i), m)));
            }
        }
        else {
            expr_ref_vector tmp(m);
            tmp.push_back(fml);
            dnf_struct.push_back(tmp);
        }
        return dnf_struct;
    }
}

static expr_ref neg_expr(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    reg_decl_plugins(m);
    arith_util a(m);
    expr *e1, *e2;

    expr_ref new_formula(m);

    if (m.is_eq(fml, e1, e2)) {
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

static expr_ref non_neg_formula(expr_ref const& fml);

static expr_ref neg_formula(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    if (m.is_and(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(neg_formula(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_disj(new_sub_formulas);
    }
    else if (m.is_or(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(neg_formula(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_conj(new_sub_formulas);
    }
    else if (m.is_not(fml)) {
        return non_neg_formula(expr_ref(to_app(fml)->get_arg(0), m));
    }
    else {
        return neg_expr(fml);
    }
}

static expr_ref non_neg_formula(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    if (m.is_and(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(non_neg_formula(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_conj(new_sub_formulas);
    }
    else if (m.is_or(fml)) {
        expr_ref_vector new_sub_formulas(m);
        for (unsigned i = 0; i < to_app(fml)->get_num_args(); ++i) {
            new_sub_formulas.push_back(non_neg_formula(expr_ref(to_app(fml)->get_arg(i), m)));
        }
        return mk_disj(new_sub_formulas);
    }
    else if (m.is_not(fml)) {
        return neg_formula(expr_ref(to_app(fml)->get_arg(0), m));
    }
    else {
        return fml;
    }
}

expr_ref neg_and_2dnf(expr_ref const& fml) {
    vector<expr_ref_vector> dnf_struct;
    dnf_struct = to_dnf_struct(neg_formula(fml));
    expr_ref_vector disjs(fml.m());
    for (unsigned i = 0; i < dnf_struct.size(); ++i) {
#ifdef PREDABST_ELIMINATE_UNSAST_DISJUNCTS
        smt_params new_param;
        smt::kernel solver(fml.m(), new_param);
        for (unsigned j = 0; j < dnf_struct[i].size(); ++j) {
            solver.assert_expr(dnf_struct[i].get(j));
        }
        if (solver.check() != l_true) {
            continue
        }
#endif
        disjs.push_back(mk_conj(dnf_struct[i]));
    }
    return mk_disj(disjs);
}

void print_expr_ref_vector(std::ostream& out, expr_ref_vector const& v, bool newline) {
    ast_manager& m = v.m();
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
    if (newline) {
        out << std::endl;
    }
}
