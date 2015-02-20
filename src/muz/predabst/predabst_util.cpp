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

static void get_conj_terms(expr* e, ast_manager& m, expr_ref_vector& terms) {
    if (m.is_and(e)) {
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            get_conj_terms(to_app(e)->get_arg(i), m, terms);
        }
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
    ast_manager& m(args.m());
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
    arith_util a(m);
    expr_ref_vector vars(m);
    expr_ref_vector todo(m);
    todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
    while (!todo.empty()) {
        expr* e = todo.back();
        todo.pop_back();
        switch (e->get_kind()) {
        case AST_VAR:
            if (!vars.contains(e)) {
                vars.push_back(e);
            }
            break;
        case AST_APP:
            if (to_app(e)->get_num_args() == 0) {
                if (!a.is_numeral(e)) {
                    if (!vars.contains(e)) {
                        vars.push_back(e);
                    }
                }
                break;
            }
            todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            break;
        case AST_FUNC_DECL:
            if (!vars.contains(e)) {
                vars.push_back(e);
            }
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
    return vars;
}

static vector<expr_ref_vector> cnf_to_dnf_struct(vector<vector<expr_ref_vector> > const& cnf_sets) {
    CASSERT("predabst", cnf_sets.size() >= 2);
    vector<expr_ref_vector> result(cnf_sets.get(0));
    for (unsigned k = 1; k < cnf_sets.size(); ++k) {
        vector<expr_ref_vector> sub_result;
        for (unsigned i = 0; i < result.size(); ++i) {
            for (unsigned j = 0; j < cnf_sets.get(k).size(); ++j) {
                expr_ref_vector entry(result[i]);
                entry.append(cnf_sets.get(k)[j]);
                sub_result.push_back(entry);
            }
        }
        result = sub_result;
    }

    return result;
}

static vector<expr_ref_vector> to_dnf_struct(expr_ref const& fml) {
    expr_ref_vector sub_formulas(fml.m());
    if (fml.m().is_and(fml)) {
        vector<vector<expr_ref_vector> > dnf_sub_structs;
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            dnf_sub_structs.push_back(to_dnf_struct(expr_ref(sub_formulas.get(i), fml.m())));
        }
        return cnf_to_dnf_struct(dnf_sub_structs);
    }
    else {
        vector<expr_ref_vector> dnf_struct;
        if (fml.m().is_or(fml)) {
            sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
            for (unsigned i = 0; i < sub_formulas.size(); ++i) {
                dnf_struct.append(to_dnf_struct(expr_ref(sub_formulas.get(i), fml.m())));
            }
        }
        else {
            expr_ref_vector tmp(fml.m());
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

    if (m.is_true(fml)) {
        new_formula = m.mk_false();
    }
    else if (m.is_false(fml)) {
        new_formula = m.mk_true();
    }
    else if (m.is_eq(fml, e1, e2)) {
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
        new_formula = fml;
    }
    return new_formula;
}

static expr_ref non_neg_formula(expr_ref const& fml);

static expr_ref neg_formula(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    expr_ref_vector sub_formulas(m);
    expr_ref_vector new_sub_formulas(m);
    if (m.is_and(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(neg_formula(expr_ref(sub_formulas.get(i), m)));
        }
        expr_ref ee1(m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
        return ee1;
    }
    else if (m.is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(neg_formula(expr_ref(sub_formulas.get(i), m)));
        }
        expr_ref ee2(m.mk_and(sub_formulas.size(), new_sub_formulas.c_ptr()), m);
        return ee2;
    }
    else if (m.is_not(fml)) {
        expr_ref ee3(to_app(fml)->get_arg(0), m);
        expr_ref ee5(non_neg_formula(ee3));
        return ee5;
    }
    else {
        expr_ref ee4(neg_expr(fml), m);
        return ee4;
    }
}

static expr_ref non_neg_formula(expr_ref const& fml) {
    ast_manager& m = fml.get_manager();
    expr_ref_vector sub_formulas(m);
    expr_ref_vector new_sub_formulas(m);
    if (m.is_and(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(non_neg_formula(expr_ref(sub_formulas.get(i), m)));
        }
        expr_ref ee1(m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
        return ee1;
    }
    else if (m.is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(non_neg_formula(expr_ref(sub_formulas.get(i), m)));
        }
        expr_ref ee2(m.mk_or(sub_formulas.size(), new_sub_formulas.c_ptr()), m);
        return ee2;
    }
    else if (m.is_not(fml)) {
        expr_ref ee3(to_app(fml)->get_arg(0), m);
        expr_ref ee5(neg_formula(ee3));
        return ee5;
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
        smt_params new_param;
        smt::kernel solver(fml.m(), new_param);
        expr_ref conj(fml.m().mk_and(dnf_struct[i].size(), dnf_struct[i].c_ptr()), fml.m());

        solver.assert_expr(conj);
        if (solver.check() == l_true) {
            disjs.push_back(conj);
        }
        solver.reset();
    }
    return expr_ref(fml.m().mk_or(disjs.size(), disjs.c_ptr()), fml.m());
}
