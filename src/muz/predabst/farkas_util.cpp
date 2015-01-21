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

void display_core_tree(core_tree m_core_tree);
void display_core_clause(ast_manager& m, core_clauses clauses);
void display_core_clause2(ast_manager& m, core_clauses2 clauses);
void display_expr_ref_vector(expr_ref_vector& vect);
void print_node_info(unsigned added_id, func_decl* sym, vector<bool> cube, unsigned r_id, vector<unsigned> parent_nodes);

struct lambda_kind {
    expr_ref m_lambda;
    lambda_kind_sort m_kind;
    unsigned m_op;
    int m_lower_bound;
    int m_upper_bound;

    lambda_kind(expr_ref in_lambda, lambda_kind_sort in_kind, unsigned in_op) :
        m_lambda(in_lambda), m_kind(in_kind), m_op(in_op),
        m_lower_bound(0),
        m_upper_bound(0) {
    }
};

expr_ref_vector vars_difference(expr_ref_vector source, expr_ref_vector to_remove);
bool mk_exists_forall_farkas(expr_ref& fml, expr_ref_vector vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds);
void mk_bilin_lambda_constraint(vector<lambda_kind> lambda_kinds, int max_lambda, expr_ref& cons);
void mk_binder(expr_ref_vector vars, expr_ref_vector args, expr_ref& cs);
static bool replace_pred(expr_ref_vector args, expr_ref_vector vars, expr_ref& pred);
bool interpolate(expr_ref_vector vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol);

template<class T>
static void push_front(vector<T>& v, T e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

static void push_front_0(expr_ref_vector& v, expr_ref e) {
    v.reverse();
    v.push_back(e);
    v.reverse();
}

static expr_ref_vector get_all_terms(expr_ref term) {
    expr_ref_vector all_facts(term.m());
    if (!arith_util(term.m()).is_mul(term.get())) {
        all_facts.push_back(term);
    }
    else {
        expr_ref_vector facts(term.m());
        facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        for (unsigned i = 0; i < facts.size(); ++i) {
            all_facts.append(get_all_terms(expr_ref(facts[i].get(), term.m())));
        }
    }
    return all_facts;
}

static void get_all_terms(expr_ref term, expr_ref_vector vars, expr_ref_vector& var_facts, expr_ref_vector& const_facts, bool& has_params) {
    if (!arith_util(term.m()).is_mul(term.get())) {
        if (vars.contains(term)) {
            var_facts.push_back(term);
        }
        else {
            const_facts.push_back(term);
            // params check ***
            if (!arith_util(term.m()).is_numeral(term)) {
                has_params = true;
            }
        }
    }
    else {
        expr_ref_vector facts(term.m());
        facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        for (unsigned i = 0; i < facts.size(); ++i) {
            get_all_terms(expr_ref(facts[i].get(), term.m()), vars, var_facts, const_facts, has_params);
        }
    }
}

void get_conj_terms(expr_ref conj, expr_ref_vector& terms) {
    if (conj.m().is_and(conj)) {
        for (unsigned i = 0; i < to_app(conj)->get_num_args(); i++) {
            get_conj_terms(expr_ref(to_app(conj)->get_arg(i), conj.m()), terms);
        }
    }
    else {
        terms.push_back(conj);
    }
}

class farkas_pred {
    expr_ref_vector m_vars;
    expr_ref_vector m_coeffs;
    unsigned m_op;
    expr_ref m_const;

    bool m_has_params;
    ast_manager& m_pred_manager;

public:

    farkas_pred(expr_ref_vector vars) : m_vars(vars), m_coeffs(vars.get_manager()),
        m_const(vars.get_manager()), m_op(1), m_has_params(false),
        m_pred_manager(vars.get_manager()) {
    }

    farkas_pred(expr_ref_vector vars, expr_ref_vector in_coeffs, unsigned in_op, expr_ref in_const) :
        m_vars(vars), m_coeffs(in_coeffs),
        m_const(in_const), m_op(in_op), m_has_params(false),
        m_pred_manager(vars.get_manager()) {
    }

    void put(expr_ref term) {
        arith_util arith(term.m());
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            m_coeffs.push_back(arith.mk_numeral(rational(0), true));
        }
        if (term.m().is_true(term)) {
            m_op = 1;
            m_const = arith.mk_numeral(rational(0), true);
        }
        else if (term.m().is_false(term)) {
            m_op = 1;
            m_const = arith.mk_numeral(rational(-1), true);
        }
        else {
            set(term);
        }
    }

    expr_ref_vector get_coeffs() {
        return m_coeffs;
    }

    expr_ref get_coeffs(unsigned i) {
        return expr_ref(m_coeffs.get(i), m_pred_manager);
    }

    unsigned get_op() {
        return m_op;
    }

    expr_ref get_const() {
        return m_const;
    }

    bool has_params() {
        return m_has_params;
    }

    void display() {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (i == 0) {
                std::cout << mk_pp(m_coeffs[i].get(), m_pred_manager) << " * " << mk_pp(m_vars[i].get(), m_pred_manager);
            }
            else {
                std::cout << " + " << mk_pp(m_coeffs[i].get(), m_pred_manager) << " * " << mk_pp(m_vars[i].get(), m_pred_manager);
            }
        }
        switch (m_op) {
        case 0:
            std::cout << " = ";
            break;
        case 1:
            std::cout << " =< ";
            break;
        case 2:
            std::cout << " >= ";
            break;
        case 3:
            std::cout << " < ";
            break;
        case 4:
            std::cout << " > ";
            break;
        default:
            std::cout << " Unknown relation! ";
            break;
        }
        std::cout << mk_pp(m_const.get(), m_pred_manager) << "\n";
        std::cout << "Params? : " << (m_has_params ? "TRUE" : "FALSE") << "\n";
    }

private:

    void rewrite_pred(expr_ref& term) {
        arith_util arith(term.m());
        expr *e1, *e2;
        if (term.m().is_eq(term, e1, e2)) {
            term = arith.mk_sub(e1, e2);
            m_op = 0;
        }
        else if (arith.is_le(term, e1, e2)) {
            term = arith.mk_sub(e1, e2);
        }
        else if (arith.is_ge(term, e1, e2)) {
            term = arith.mk_sub(e2, e1);
        }
        else if (arith.is_lt(term, e1, e2)) {
            term = arith.mk_sub(arith.mk_sub(e1, e2), arith.mk_numeral(rational(-1), true));
        }
        else if (arith.is_gt(term, e1, e2)) {
            term = arith.mk_sub(arith.mk_sub(e2, e1), arith.mk_numeral(rational(-1), true));
        }
        else {
            std::cout << "after subst fml: " << mk_pp(term, term.m()) << "\n";
            std::cout << "Unable to recognize predicate \n";
            throw(term);
        }
        th_rewriter rw(term.m());
        rw(term);
    }

    void set(expr_ref& term) {
        arith_util arith(m_pred_manager);
        rewrite_pred(term);
        expr_ref_vector p_coeffs(m_pred_manager), p_vars(m_pred_manager), p_const_facts(m_pred_manager), add_facts(m_pred_manager);
        if (arith.is_add(term.get())) {
            add_facts.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        }
        else {
            add_facts.push_back(term);
        }
        for (unsigned i = 0; i < add_facts.size(); ++i) {
            expr_ref_vector mul_facts(m_pred_manager), var_mul_facts(m_pred_manager), const_mul_facts(m_pred_manager);
            expr_ref mul_term(add_facts[i].get(), m_pred_manager);
            get_all_terms(mul_term, m_vars, var_mul_facts, const_mul_facts, m_has_params);
            SASSERT(var_mul_facts.size() <= 1);
            if (var_mul_facts.size() == 0) {
                p_const_facts.push_back(add_facts[i].get());
            }
            else if (const_mul_facts.size() == 0) {
                p_vars.push_back(add_facts[i].get());
                p_coeffs.push_back(arith.mk_numeral(rational(1), true));
            }
            else if (const_mul_facts.size() == 1) {
                p_vars.push_back(var_mul_facts[0].get());
                p_coeffs.push_back(const_mul_facts[0].get());
            }
            else {
                p_vars.push_back(var_mul_facts[0].get());
                p_coeffs.push_back(arith.mk_mul(const_mul_facts.size(), const_mul_facts.c_ptr()));
            }
        }
        if (p_const_facts.size() == 0) {
            m_const = arith.mk_numeral(rational(0), true);
        }
        else if (p_const_facts.size() == 1) {
            m_const = arith.mk_uminus(p_const_facts[0].get());
        }
        else {
            m_const = arith.mk_uminus(arith.mk_add(p_const_facts.size(), p_const_facts.c_ptr()));
        }
        th_rewriter rw(m_pred_manager);
        rw(m_const);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            for (unsigned j = 0; j < p_vars.size(); ++j) {
                if (m_vars[i].get() == p_vars[j].get()) {
                    m_coeffs.set(i, p_coeffs[j].get());
                    p_vars.erase(j);
                    p_coeffs.erase(j);
                    break;
                }
            }
        }
    }
};

class farkas_conj {
    expr_ref_vector m_vars;
    vector<expr_ref_vector> m_set_coeffs;
    vector<unsigned> m_set_op;
    vector<expr_ref> m_set_const;

    unsigned m_param_pred_count;
    ast_manager m_conj_manager;


public:
    farkas_conj(expr_ref_vector vars) :
        m_vars(vars), m_param_pred_count(0), m_conj_manager(vars.get_manager()) {
    }

    void add(farkas_pred& f_pred) {
        if (m_set_coeffs.size() == 0) {
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                expr_ref_vector init_coeff(m_conj_manager);
                init_coeff.push_back(f_pred.get_coeffs(i));
                m_set_coeffs.push_back(init_coeff);
            }
            m_set_op.push_back(f_pred.get_op());
            m_set_const.push_back(f_pred.get_const());
            if (f_pred.has_params()) {
                m_param_pred_count++;
            }
        }
        else {
            if (f_pred.has_params()) {
                for (unsigned i = 0; i < m_vars.size(); ++i) {
                    push_front_0(m_set_coeffs[i], f_pred.get_coeffs(i));
                }
                push_front(m_set_op, f_pred.get_op());
                push_front(m_set_const, f_pred.get_const());
                m_param_pred_count++;
            }
            else {
                for (unsigned i = 0; i < m_vars.size(); ++i) {
                    m_set_coeffs[i].push_back(f_pred.get_coeffs(i));
                }
                m_set_op.push_back(f_pred.get_op());
                m_set_const.push_back(f_pred.get_const());
            }
        }
    }

    expr_ref get_conj_coeffs(unsigned i, unsigned j) {
        return expr_ref(m_set_coeffs.get(i).get(j), m_conj_manager);
    }

    expr_ref get_conj_const(unsigned i) {
        return expr_ref(m_set_const.get(i), m_conj_manager);
    }

    unsigned get_ops(unsigned i) {
        return  m_set_op.get(i);
    }

    unsigned conj_size() {
        return m_set_op.size();
    }

    unsigned get_param_pred_count() {
        return m_param_pred_count;
    }

    void display() {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            std::cout << mk_pp(m_vars[i].get(), m_conj_manager) << "   ";
        }
        std::cout << "\n";
        for (unsigned i = 0; i < m_set_coeffs[0].size(); ++i) {
            for (unsigned j = 0; j < m_vars.size(); ++j) {
                std::cout << mk_pp(m_set_coeffs[j][i].get(), m_conj_manager) << "   ";
            }
            std::cout << m_set_op[i] << "   " << mk_pp(m_set_const[i].get(), m_conj_manager) << "\n";
        }
    }
};

class farkas_imp {
    expr_ref_vector m_vars;
    farkas_conj m_lhs;
    farkas_pred m_rhs;
    expr_ref_vector m_lambdas;
    expr_ref_vector m_solutions;
    expr_ref m_constraints;

    vector<lambda_kind> m_lambda_kinds;
    bool m_mk_lambda_kinds;

    ast_manager& m_imp_manager;

public:
    farkas_imp(expr_ref_vector vars, bool mk_lambda_kinds = false) : m_vars(vars), m_lhs(vars), m_rhs(vars),
        m_lambdas(vars.get_manager()), m_solutions(vars.get_manager()),
        m_constraints((vars.get_manager()).mk_true(), vars.get_manager()),
        m_mk_lambda_kinds(mk_lambda_kinds),
        m_imp_manager(vars.get_manager()) {
    }

    void set(expr_ref lhs_term, expr_ref rhs_term) {
        expr_ref_vector conjs(m_imp_manager);
        conjs.append(to_app(lhs_term)->get_num_args(), to_app(lhs_term)->get_args());
        for (unsigned i = 0; i < conjs.size(); ++i) {
            farkas_pred f_pred(m_vars);
            f_pred.put(expr_ref(conjs.get(i), m_imp_manager));
            m_lhs.add(f_pred);
        }
        m_rhs.put(rhs_term);
        set_constraint();
    }

    bool solve_constraint() {
        smt_params new_param;;
        smt::kernel solver(m_imp_manager, new_param);
        solver.assert_expr(m_constraints);
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            expr_ref solution(m_imp_manager);
            for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
                if (modref.get()->eval(m_lambdas.get(j), solution, true)) {
                    m_solutions.push_back(solution);
                }
                else {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    expr_ref_vector get_lambdas() {
        return m_lambdas;
    }

    expr_ref_vector get_solutions() {
        return m_solutions;
    }

    expr_ref get_constraints() {
        return m_constraints;
    }

    vector<lambda_kind> get_lambda_kinds() {
        return m_lambda_kinds;
    }

    void display() {
        ast_manager m = m_vars.get_manager();
        std::cout << "LHS: \n";
        m_lhs.display();
        std::cout << "RHS: \n";
        m_rhs.display();
        std::cout << "Constraint: \n" << mk_pp(m_constraints.get(), m) << "\n";
        if (m_solutions.size() > 0) {
            std::cout << "Solutions: \n";
        }
        for (unsigned i = 0; i < m_solutions.size(); ++i) {
            std::cout << mk_pp(m_lambdas[i].get(), m) << " --> " << mk_pp(m_solutions[i].get(), m) << "\n";
        }
    }

private:

    void set_constraint() {
        arith_util arith(m_imp_manager);
        SASSERT(m_lhs.get_param_pred_count() > 0);

        for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
            m_lambdas.push_back(expr_ref(m_imp_manager.mk_fresh_const("t", arith.mk_int()), m_imp_manager));
            if (m_lhs.get_ops(i) == 1) {
                m_constraints = m_imp_manager.mk_and(m_constraints, arith.mk_ge(m_lambdas.get(i), arith.mk_numeral(rational(0), true)));
            }
        }

        if (m_lhs.get_param_pred_count() == 1 && m_lhs.get_ops(0) != 0) {
            m_constraints = m_imp_manager.mk_and(m_constraints, m_imp_manager.mk_eq(m_lambdas.get(0), arith.mk_numeral(rational(1), true)));
        }

        if (m_mk_lambda_kinds) {
            set_lambda_kinds();
        }

        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref sum(arith.mk_numeral(rational(0), true), m_imp_manager);
            for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
                sum = arith.mk_add(sum, arith.mk_mul(m_lambdas.get(j), m_lhs.get_conj_coeffs(i, j)));
            }
            m_constraints = m_imp_manager.mk_and(m_constraints, m_imp_manager.mk_eq(sum, m_rhs.get_coeffs(i)));
        }

        expr_ref sum_const(arith.mk_numeral(rational(0), true), m_imp_manager);
        for (unsigned j = 0; j < m_lhs.conj_size(); ++j) {
            sum_const = arith.mk_add(sum_const, arith.mk_mul(m_lambdas.get(j), m_lhs.get_conj_const(j)));
        }
        m_constraints = m_imp_manager.mk_and(m_constraints, arith.mk_le(sum_const, m_rhs.get_const()));
    }

    void set_lambda_kinds() {
        arith_util arith(m_imp_manager);
        if (m_lhs.get_param_pred_count() == 1) {
            if (m_lhs.get_ops(0) == 0) {
                m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(0), m_imp_manager), bilin_sing, m_lhs.get_ops(0)));
            }
        }
        else {
            for (unsigned i = 0; i < m_lhs.conj_size(); ++i) {
                if (i < m_lhs.get_param_pred_count()) {
                    m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m_imp_manager), bilin, m_lhs.get_ops(i)));
                }
                else {
                    m_lambda_kinds.push_back(lambda_kind(expr_ref(m_lambdas.get(i), m_imp_manager), lin, m_lhs.get_ops(i)));
                }
            }
        }
    }
};

bool exists_valid(expr_ref& formula, expr_ref_vector& vars, app_ref_vector& q_vars, expr_ref& constraint_st);

vector<expr_ref_vector> cnf_to_dnf_struct(vector<vector<expr_ref_vector> > cnf_sets) {
    SASSERT(cnf_sets.size() >= 2);
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

expr_ref neg_expr(expr_ref& fml) {
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

vector<expr_ref_vector> to_dnf_struct(expr_ref fml) {
    vector<expr_ref_vector> dnf_struct;
    expr_ref_vector sub_formulas(fml.m());
    if (fml.m().is_and(fml)) {
        vector<vector<expr_ref_vector> > dnf_sub_structs;
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            dnf_sub_structs.push_back(to_dnf_struct(expr_ref(sub_formulas[i].get(), fml.m())));
        }
        return cnf_to_dnf_struct(dnf_sub_structs);
    }
    else if (fml.m().is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            dnf_struct.append(to_dnf_struct(expr_ref(sub_formulas[i].get(), fml.m())));
        }
    }
    else {
        expr_ref_vector tmp(fml.m());
        tmp.push_back(fml);
        dnf_struct.push_back(tmp);
    }
    return dnf_struct;
}

expr_ref non_neg_formula(expr_ref fml);

expr_ref neg_formula(expr_ref fml) {
    ast_manager& m = fml.get_manager();
    expr_ref_vector sub_formulas(m);
    expr_ref_vector new_sub_formulas(m);
    if (m.is_and(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(neg_formula(expr_ref(sub_formulas[i].get(), m)));
        }
        expr_ref ee1(m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
        return ee1;
    }
    else if (m.is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(neg_formula(expr_ref(sub_formulas[i].get(), m)));
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

expr_ref non_neg_formula(expr_ref fml) {
    ast_manager& m = fml.get_manager();
    expr_ref_vector sub_formulas(m);
    expr_ref_vector new_sub_formulas(m);
    if (m.is_and(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(non_neg_formula(expr_ref(sub_formulas[i].get(), m)));
        }
        expr_ref ee1(m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr()), m);
        return ee1;
    }
    else if (m.is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(non_neg_formula(expr_ref(sub_formulas[i].get(), m)));
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

void neg_and_2dnf(expr_ref& fml, expr_ref& fml2) {
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
    fml2 = expr_ref(fml.m().mk_or(disjs.size(), disjs.c_ptr()), fml.m());
}

void mk_binder(expr_ref_vector vars, expr_ref_vector args, expr_ref& cs) {
    SASSERT(vars.size() == args.size());
    for (unsigned i = 0; i < vars.size(); i++) {
        if (vars.m().is_true(cs)) {
            cs = vars.m().mk_eq(vars.get(i), args.get(i));
        }
        else {
            cs = vars.m().mk_and(cs, vars.m().mk_eq(vars.get(i), args.get(i)));
        }
    }
}

bool exists_valid(expr_ref& fml, expr_ref_vector& vars, app_ref_vector& q_vars, expr_ref& constraint_st) {
    ast_manager& m = fml.m();
    expr_ref norm_fml(fml.m());
    neg_and_2dnf(fml, norm_fml);
    SASSERT(fml.m().is_or(norm_fml));
    expr_ref_vector disjs(fml.m());
    disjs.append(to_app(norm_fml)->get_num_args(), to_app(norm_fml)->get_args());
    for (unsigned i = 0; i < disjs.size(); ++i) {
        expr_ref each_disj(disjs.get(i), fml.m());
        app_ref_vector q_vars_disj(q_vars);
        qe_lite ql1(fml.m());
        ql1(q_vars_disj, each_disj);
        farkas_imp f_imp(vars);
        f_imp.set(expr_ref(each_disj, fml.m()), expr_ref(fml.m().mk_false(), fml.m()));
        if (!f_imp.solve_constraint()) {
            return false;
        }
        constraint_st = fml.m().mk_and(constraint_st, f_imp.get_constraints());
    }
    return true;
}

bool mk_exists_forall_farkas(expr_ref& fml, expr_ref_vector vars, expr_ref& constraint_st, bool mk_lambda_kinds, vector<lambda_kind>& all_lambda_kinds) {
    expr_ref norm_fml(fml.m());
    neg_and_2dnf(fml, norm_fml);
    SASSERT(fml.m().is_or(norm_fml));
    expr_ref_vector disjs(fml.m());
    disjs.append(to_app(norm_fml)->get_num_args(), to_app(norm_fml)->get_args());
    for (unsigned i = 0; i < disjs.size(); ++i) {
        farkas_imp f_imp(vars, mk_lambda_kinds);
        f_imp.set(expr_ref(disjs[i].get(), fml.m()), expr_ref(fml.m().mk_false(), fml.m()));
        if (f_imp.solve_constraint()) {
            constraint_st = fml.m().mk_and(constraint_st, f_imp.get_constraints());
            all_lambda_kinds.append(f_imp.get_lambda_kinds());
        }
        else {
            return false;
        }
    }
    return true;
}

bool well_founded(expr_ref_vector vsws, expr_ref& LHS, expr_ref& sol_bound, expr_ref& sol_decrease) {
    ast_manager& m = LHS.get_manager();
    arith_util arith(m);
    if (m.is_true(LHS) || !m.is_and(LHS) || to_app(LHS)->get_num_args() <= 1 || (vsws.size() % 2) != 0) {
        return false;
    }

    expr_ref_vector vs(m), ws(m);
    bool hasv = false, hasvp = false;
    expr_ref_vector LHS_vars(get_all_pred_vars(LHS));
    for (unsigned i = 0; i < vsws.size(); i++) {
        if (i < (vsws.size() / 2)) {
            vs.push_back(vsws.get(i));
            if (!hasv && LHS_vars.contains(vsws.get(i))) {
                hasv = true;
            }
        }
        else {
            ws.push_back(vsws.get(i));
            if (!hasvp && LHS_vars.contains(vsws.get(i))) {
                hasvp = true;
            }
        }

    }

    if (!hasv || !hasvp) {
        return false;
    }

    app_ref_vector q_vars(m);
    for (unsigned j = 0; j < LHS_vars.size(); j++) {
        if (!vsws.contains(LHS_vars.get(j))) q_vars.push_back(to_app(LHS_vars.get(j)));
    }

    expr_ref_vector params(m);
    expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
    expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        params.push_back(param);
        sum_psvs = arith.mk_add(sum_psvs.get(), arith.mk_mul(param.get(), vs[i].get()));
        sum_psws = arith.mk_add(sum_psws.get(), arith.mk_mul(param.get(), ws[i].get()));
    }

    expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);
    params.push_back(delta0);

    expr_ref bound(arith.mk_ge(sum_psvs, delta0), m);
    expr_ref decrease(arith.mk_lt(sum_psws, sum_psvs), m);
    expr_ref to_solve(m.mk_or(m.mk_not(LHS), m.mk_and(bound, decrease)), m);

    std::cout << "bound: " << mk_pp(bound, m) << "\n";
    std::cout << "decrease: " << mk_pp(decrease, m) << "\n";
    expr_ref constraint_st(m.mk_true(), m);
    if (exists_valid(to_solve, vsws, q_vars, constraint_st)) {
        smt_params new_param;
        smt::kernel solver(m, new_param);
        solver.assert_expr(constraint_st);
        if (solver.check() == l_true) {
            expr_ref_vector values(m);
            model_ref modref;
            solver.get_model(modref);
            if (modref.get()->eval(bound.get(), sol_bound) && modref.get()->eval(decrease.get(), sol_decrease)) {
                return true;
            }
            return false; // when does it happen?
        }
        return false; //unsat param
    }
    return false; //unsat lambda
}

void well_founded_cs(expr_ref_vector vsws, expr_ref& bound, expr_ref& decrease) {
    ast_manager& m = vsws.get_manager();
    arith_util arith(m);

    expr_ref_vector vs(m), ws(m);
    for (unsigned i = 0; i < vsws.size(); i++) {
        if (i < (vsws.size() / 2)) {
            vs.push_back(vsws.get(i));
        }
        else {
            ws.push_back(vsws.get(i));
        }
    }
    expr_ref_vector params(m);
    expr_ref sum_psvs(arith.mk_numeral(rational(0), true), m);
    expr_ref sum_psws(arith.mk_numeral(rational(0), true), m);

    for (unsigned i = 0; i < vs.size(); ++i) {
        expr_ref param(m.mk_fresh_const("p", arith.mk_int()), m);
        params.push_back(param);
        sum_psvs = arith.mk_add(sum_psvs.get(), arith.mk_mul(param.get(), vs[i].get()));
        sum_psws = arith.mk_add(sum_psws.get(), arith.mk_mul(param.get(), ws[i].get()));
    }

    expr_ref delta0(m.mk_const(symbol("delta0"), arith.mk_int()), m);
    params.push_back(delta0);

    bound = arith.mk_ge(sum_psvs, delta0);
    decrease = arith.mk_lt(sum_psws, sum_psvs);

    std::cout << "bound: " << mk_pp(bound, m) << "\n";
    std::cout << "decrease: " << mk_pp(decrease, m) << "\n";
}

void mk_bilin_lambda_constraint(vector<lambda_kind> lambda_kinds, int max_lambda, expr_ref& cons) {
    ast_manager& m = cons.get_manager();
    arith_util arith(m);

    expr_ref n1(arith.mk_numeral(rational(1), true), m);
    expr_ref nminus1(arith.mk_numeral(rational(-1), true), m);

    int min_lambda = -1 * max_lambda;

    for (unsigned i = 0; i < lambda_kinds.size(); i++) {
        if (lambda_kinds[i].m_kind == bilin_sing) {
            cons = m.mk_and(cons, m.mk_or(m.mk_eq(lambda_kinds[i].m_lambda, nminus1), m.mk_eq(lambda_kinds[i].m_lambda.get(), n1)));
        }
        else if (lambda_kinds[i].m_kind == bilin) {
            if (lambda_kinds[i].m_op != 0) {
                min_lambda = 0; // operator not equality
            }
            expr_ref bilin_disj(m.mk_true(), m);
            for (int j = min_lambda; j <= max_lambda; j++) {
                bilin_disj = m.mk_or(bilin_disj, m.mk_eq(lambda_kinds[i].m_lambda.get(), arith.mk_numeral(rational(j), true)));
            }
            cons = m.mk_and(cons, bilin_disj);
        }
    }
}

void mk_bound_pairs(vector<lambda_kind>& lambda_kinds, int lin_max_lambda, int bilin_max_lambda) {
    for (unsigned i = 0; i < lambda_kinds.size(); i++) {
        if (lambda_kinds[i].m_kind == bilin_sing) {
            lambda_kinds[i].m_lower_bound = -1;
            lambda_kinds[i].m_upper_bound = 1;
        }
        else {
            int min_lambda;
            if (lambda_kinds[i].m_kind == bilin) {
                min_lambda = -1 * bilin_max_lambda;
                lambda_kinds[i].m_upper_bound = bilin_max_lambda;
            }
            else {
                min_lambda = -1 * lin_max_lambda;
                lambda_kinds[i].m_upper_bound = lin_max_lambda;
            }

            if (lambda_kinds[i].m_op == 0) {
                lambda_kinds[i].m_lower_bound = min_lambda;
            }
            else {
                lambda_kinds[i].m_lower_bound = 0;
            }

        }
    }
}

expr_ref_vector get_all_pred_vars(expr_ref& fml) {
    ast_manager& m = fml.get_manager();
    arith_util a(m);
    expr_ref_vector m_todo(m);
    expr_ref_vector vars(m);
    m_todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
    while (!m_todo.empty()) {
        expr* e = m_todo.back();
        m_todo.pop_back();
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
            m_todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
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

void display_core_tree(core_tree m_core_tree) {
    for (unsigned i = 0; i < m_core_tree.size(); i++) {
        std::cout << "core_hname: " << m_core_tree.find(i)->first << ", core_id: " << m_core_tree.find(i)->second.first.first << ", core_ids: [";
        for (unsigned j = 0; j < m_core_tree.find(i)->second.first.second.size(); j++) {
            std::cout << " " << m_core_tree.find(i)->second.first.second.get(j);
        }
        std::cout << "], core_body_names: [";
        for (unsigned j = 0; j < m_core_tree.find(i)->second.second.size(); j++) {
            std::cout << " " << m_core_tree.find(i)->second.second.get(j);
        }
        std::cout << "]\n";
    }

}

void display_core_clause(ast_manager& m, core_clauses clauses) {
    core_clauses::iterator st = clauses.begin(), end = clauses.end();
    for (; st != end; st++) {
        std::cout << "clause --> " << st->first << " [";
        for (unsigned i = 0; i < st->second.first.size(); i++) {
            std::cout << mk_pp(st->second.first.get(i), m) << " ";
        }
        std::cout << "] : " << mk_pp(st->second.second.first, m) << " [";
        for (unsigned i = 0; i < st->second.second.second.size(); i++) {
            std::cout << mk_pp(st->second.second.second.get(i), m) << " ";
        }
        std::cout << "]\n";
    }
}

void display_core_clause2(ast_manager& m, core_clauses2 clauses) {
    for (unsigned j = 0; j < clauses.size(); j++) {
        std::cout << "clause --> " << clauses.get(j).first.str() << " [";
        for (unsigned i = 0; i < clauses.get(j).second.first.size(); i++) {
            std::cout << mk_pp(clauses.get(j).second.first.get(i), m) << " ";
        }
        std::cout << "] : " << mk_pp(clauses.get(j).second.second.first, m) << " [";
        for (unsigned i = 0; i < clauses.get(j).second.second.second.size(); i++) {
            std::cout << mk_pp(clauses.get(j).second.second.second.get(i), m) << " ";
        }
        std::cout << "]\n";
    }
}

void display_expr_ref_vector(expr_ref_vector& vect) {
    std::cout << "expr vect --> [";
    for (unsigned i = 0; i < vect.size(); i++) {
        std::cout << mk_pp(vect.get(i), vect.m()) << " ";
    }
    std::cout << "]\n";
}

expr_ref_vector vars_difference(expr_ref_vector source, expr_ref_vector to_remove) {
    expr_ref_vector diff(source.get_manager());
    for (unsigned i = 0; i < source.size(); i++) {
        if (!to_remove.contains(source[i].get())) {
            diff.push_back(source[i].get());
        }
    }
    return diff;
}

expr_ref rel_template_suit::subst_template_body(expr_ref fml, vector<rel_template> rel_templates, expr_ref_vector& args_coll) {
    ast_manager& m = fml.get_manager();
    expr_ref new_formula(m);
    expr_ref_vector sub_formulas(m);
    expr_ref_vector new_sub_formulas(m);
    if (m.is_and(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas[i].get(), m), rel_templates, args_coll).get());
        }
        new_formula = m.mk_and(new_sub_formulas.size(), new_sub_formulas.c_ptr());
    }
    else if (m.is_or(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        for (unsigned i = 0; i < sub_formulas.size(); ++i) {
            new_sub_formulas.push_back(subst_template_body(expr_ref(sub_formulas[i].get(), m), rel_templates, args_coll).get());
        }
        new_formula = m.mk_or(new_sub_formulas.size(), new_sub_formulas.c_ptr());

    }
    else if (m.is_not(fml)) {
        sub_formulas.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        new_formula = m.mk_not(subst_template_body(expr_ref(sub_formulas[0].get(), m), rel_templates, args_coll));
    }
    else {
        if (m_names.contains(to_app(fml)->get_decl()->get_name())) {
            for (unsigned i = 0; i < rel_templates.size(); i++) {
                if (to_app(fml)->get_decl()->get_name() == rel_templates.get(i).m_head->get_decl()->get_name()) {
                    expr_ref cs(m_rel_templates_orig.get(i).m_body);
                    expr_ref_vector args(m, to_app(fml)->get_decl()->get_arity(), to_app(fml)->get_args());
                    args_coll.append(args);
                    args.append(m_params);
                    args.reverse();
                    m_var_subst(cs, args.size(), args.c_ptr(), cs);
                    return cs;
                }
            }
        }
        return fml;
    }
    return new_formula;
}

bool interpolate(expr_ref_vector vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol) {
    ast_manager& m = vars.get_manager();
    arith_util arith(m);
    expr_ref_vector params(m);
    expr_ref sum_vars(arith.mk_numeral(rational(0), true), m);

    app_ref_vector q_varsA(m);
    qe_lite ql(fmlA.m());
    expr_ref_vector all_varsA(get_all_pred_vars(fmlA));
    for (unsigned j = 0; j < all_varsA.size(); j++) {
        if (!vars.contains(all_varsA.get(j))) {
            q_varsA.push_back(to_app(all_varsA.get(j)));
        }
    }

    ql(q_varsA, fmlA);
    app_ref_vector q_varsB(fmlB.m());
    expr_ref_vector all_varsB(get_all_pred_vars(fmlB));
    for (unsigned j = 0; j < all_varsB.size(); j++) {
        if (!vars.contains(all_varsB.get(j))) {
            q_varsB.push_back(to_app(all_varsB.get(j)));
        }
    }
    ql(q_varsB, fmlB);
    for (unsigned i = 0; i < vars.size(); ++i) {
        expr_ref param(m.mk_fresh_const("i", arith.mk_int()), m);
        params.push_back(param);
        sum_vars = arith.mk_add(sum_vars, arith.mk_mul(param, vars.get(i)));
    }
    expr_ref ic(m.mk_const(symbol("ic"), arith.mk_int()), m);
    params.push_back(ic);
    expr_ref fmlQ(arith.mk_le(sum_vars, ic), m);

    expr_ref to_solve(m.mk_and(m.mk_or(m.mk_not(fmlA), fmlQ), m.mk_or(m.mk_not(fmlQ), m.mk_not(fmlB))), m);

    app_ref_vector q_vars(m);
    expr_ref constraint_st(m.mk_true(), m);
    if (exists_valid(to_solve, vars, q_vars, constraint_st)) {
        smt_params new_param;
        smt::kernel solver(m, new_param);
        solver.assert_expr(constraint_st);
        if (solver.check() == l_true) {
            expr_ref_vector values(m);
            model_ref modref;
            solver.get_model(modref);
            if (modref.get()->eval(fmlQ.get(), fmlQ_sol)) {
                return true;
            }
            // when does it happen?
        }
    }
    return false;
}

bool solve_clauses(core_clauses clauses, ast_manager& m, vector<refine_pred_info>& interpolants) {
    core_clauses::iterator st = clauses.begin(), end = clauses.end();
    expr_ref_vector vars(m);
    for (core_clauses::iterator it = st; it != end; it++) {
        vars.append(it->second.first);
    }
    end--;
    for (int i = clauses.size() - 1; i >= 1; i--) {
        std::cout << "Interpolation step :" << clauses.size() - i << "\n";
        expr_ref fmlA(m.mk_true(), m);
        expr_ref fmlB(m.mk_true(), m);
        int j = clauses.size() - 1;
        core_clauses::iterator end2 = end;
        for (; j >= i; j--, end2--) {
            fmlA = m.mk_and(fmlA, end2->second.second.first);
        }
        for (; j >= 0; j--, end2--) {
            fmlB = m.mk_and(fmlB, end2->second.second.first);
        }
        expr_ref fmlQ_sol(m);
        if (interpolate(vars, fmlA, fmlB, fmlQ_sol)) {
            interpolants.push_back(refine_pred_info(fmlQ_sol, get_all_pred_vars(fmlQ_sol)));
        }
        else {
            std::cout << "Interpolant not found!\n";
        }
    }
    return (interpolants.size() > 0);
}

bool solve_clauses2(core_clauses clauses, ast_manager& m, vector<refine_pred_info>& interpolants) {
    core_clauses::iterator st = clauses.begin(), end = clauses.end();
    end--;
    for (int i = clauses.size() - 1; i >= 1; i--) {
        expr_ref fmlA(m.mk_true(), m);
        expr_ref fmlB(m.mk_true(), m);
        int j = clauses.size() - 1;
        core_clauses::iterator end2 = end;
        for (; j >= i; j--, end2--) {
            mk_conj(fmlA, end2->second.second.first, fmlA);
        }
        core_clauses::iterator end4 = end2; end4++;
        expr_ref_vector vars(end4->second.first);
        for (; j >= 0; j--, end2--) {
            mk_conj(fmlB, end2->second.second.first, fmlB);
        }
        expr_ref fmlQ_sol(m);

        if (interpolate(vars, fmlA, fmlB, fmlQ_sol)) {
            interpolants.push_back(refine_pred_info(fmlQ_sol, get_all_pred_vars(fmlQ_sol)));
        }
    }
    return (interpolants.size() > 0);
}

void get_interpolant_pred(expr_ref_vector args, expr_ref_vector vars, vector<refine_pred_info> interpolants, expr_ref_vector& in_preds) {
    bool is_args_pred;
    for (unsigned i = 0; i < interpolants.size(); i++) {
        is_args_pred = true;
        for (unsigned j = 0; j < interpolants.get(i).pred_vars.size(); j++) {
            if (!args.contains(interpolants.get(i).pred_vars.get(j))) {
                is_args_pred = false;
                break;
            }
        }
        if (is_args_pred) {
            expr_ref in_pred(interpolants.get(i).pred);
            replace_pred(args, vars, in_pred);
            if (!in_preds.contains(in_pred)) {
                in_preds.push_back(in_pred);
            }
        }
    }
}

static bool replace_pred(expr_ref_vector args, expr_ref_vector vars, expr_ref& pred) {
    ast_manager& m = pred.m();
    arith_util arith(pred.m());
    expr *e1, *e2;
    if (pred.m().is_eq(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = m.mk_eq(ee1, ee2);
    }
    else if (arith.is_le(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = arith.mk_le(ee1, ee2);
    }
    else if (arith.is_ge(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = arith.mk_ge(ee1, ee2);
    }
    else if (arith.is_lt(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = arith.mk_lt(ee1, ee2);
    }
    else if (arith.is_gt(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = arith.mk_gt(ee1, ee2);
    }
    else if (arith.is_add(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = arith.mk_add(ee1, ee2);
    }
    else if (arith.is_mul(pred, e1, e2)) {
        expr_ref ee1(e1, m), ee2(e2, m);
        replace_pred(args, vars, ee1);
        replace_pred(args, vars, ee2);
        pred = arith.mk_mul(ee1, ee2);
    }
    else if (m.is_not(pred, e1)) {
        expr_ref ee1(e1, m);
        replace_pred(args, vars, ee1);
        pred = m.mk_not(ee1);
    }
    else if (to_app(pred)->get_num_args() == 0) {
        if (args.contains(pred)) {
            for (unsigned i = 0; i < args.size(); i++) {
                if (args.get(i) == pred) {
                    pred = vars.get(i);
                    break;
                }
            }
        }
    }
    else {
        std::cout << "after subst fml: " << mk_pp(pred, pred.m()) << "\n";
        std::cout << "Unable to recognize predicate \n";
        return false;
    }
    return true;
}

void mk_conj(expr_ref_vector terms, expr_ref& conj) {
    if (terms.size() == 0) {
        conj = terms.m().mk_true();
    }
    else if (terms.size() == 1) {
        conj = terms.get(0);
    }
    else {
        conj = terms.m().mk_and(terms.size(), terms.c_ptr());
    }
}

void mk_conj(expr_ref term1, expr_ref term2, expr_ref& conj) {
    if (term1.m().is_true(term1)) {
        conj = term2;
    }
    else if (term1.m().is_true(term2)) {
        conj = term1;
    }
    else {
        conj = term1.m().mk_and(term1, term2);
    }
}

void print_node_info(unsigned added_id, func_decl* sym, vector<bool> cube, unsigned r_id, vector<unsigned> parent_nodes) {
    std::cout << "Node added: (" << added_id << ", " << sym->get_name().str() << ", " << r_id << ", [";
    for (unsigned i = 0; i < parent_nodes.size(); i++) {
        std::cout << parent_nodes.get(i) << " ";
    }
    std::cout << "]) " << ", [";
    for (unsigned i = 0; i < cube.size(); i++) {
        std::cout << cube.get(i) << " ";
    }
    std::cout << "]) \n";
}

void rel_template_suit::init_template_instantiate() {
    std::cout << "init_template_instantiate\n";
    if (m_rel_templates.size() == 0) {
        return;
    }
    display();
    std::cout << "m_extras  : " << mk_pp(m_extras, m_rel_manager) << "\n";
    smt_params new_param;
    smt::kernel solver(m_rel_manager, new_param);
    solver.assert_expr(m_extras);
    solver.display(std::cout);
    if (solver.check() == l_true) {
        solver.get_model(m_modref);
        for (unsigned i = 0; i < m_rel_templates.size(); i++) {
            expr_ref instance(m_rel_manager);
            if (m_modref.get()->eval(m_rel_templates[i].m_body, instance)) {
                m_rel_template_instances.push_back(rel_template(m_rel_templates[i].m_head, instance));
            }
        }
    }
}

bool rel_template_suit::get_orig_template(app* in_head, expr_ref& body) {
    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        if (m_rel_templates.get(i).m_head->get_decl()->get_name() == in_head->get_decl()->get_name()) {
            body = m_rel_templates_orig.get(i).m_body;
            return true;
        }
    }
    return false;
}

bool rel_template_suit::get_instance(app* head, expr_ref& body, expr_ref_vector& vars) {
    for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
        if (m_rel_template_instances[i].m_head->get_decl()->get_name() == head->get_decl()->get_name()) {
            body = m_rel_template_instances[i].m_body;
            vars.append(m_rel_template_instances[i].m_head->get_decl()->get_arity(), m_rel_template_instances[i].m_head->get_args());
            return true;
        }
    }
    return false;
}

bool rel_template_suit::constrain_template(expr_ref fml) {
    if (m_rel_templates.size() == 0) {
        return false;
    }
    std::cout << "constrain_template begin ...\n";
    reset();
    display();
    if (!fml.m().is_true(fml)) {
        m_acc = fml.m().mk_and(fml, m_acc);
    }
    expr_ref_vector args_coll(m_rel_manager);
    expr_ref c1(subst_template_body(m_acc, m_rel_templates, args_coll), m_rel_manager);
    args_coll.append(m_temp_subst);

    expr_ref constraint_st(m_rel_manager.mk_true(), m_rel_manager);
    vector<lambda_kind> all_lambda_kinds;
    if (mk_exists_forall_farkas(c1, args_coll, constraint_st, true, all_lambda_kinds)) {
        expr_ref lambda_cs(m_rel_manager.mk_true(), m_rel_manager);
        int max_lambda = 2;
        mk_bilin_lambda_constraint(all_lambda_kinds, max_lambda, lambda_cs);

        smt_params new_param;
        smt::kernel solver(m_rel_manager, new_param);
        solver.assert_expr(constraint_st);
        solver.assert_expr(lambda_cs);
        solver.assert_expr(m_extras);
        if (solver.check() == l_true) {
            model_ref modref;
            solver.get_model(modref);
            for (unsigned i = 0; i < m_rel_templates.size(); i++) {
                expr_ref instance(m_rel_manager);
                if (modref.get()->eval(m_rel_templates[i].m_body, instance)) {
                    std::cout << "instance  : " << mk_pp(instance, m_rel_manager) << "\n";
                    m_rel_template_instances.push_back(rel_template(m_rel_templates[i].m_head, instance));

                }
                else {
                    // at least one template can't have a satisfying instance
                    return false;
                }
            }
            // each template has a satisfying instance
            return true;
        }
    }
    return false;
}

void refine_cand_info::insert(symbol sym, expr_ref_vector args) {
    for (unsigned i = 0; i < m_allrels_info.size(); i++) {
        if (m_allrels_info.get(i).first == sym) {
            m_allrels_info.get(i).second.push_back(args);
            return;
        }
    }
    vector<expr_ref_vector> new_args;
    new_args.push_back(args);
    m_allrels_info.push_back(std::make_pair(sym, new_args));
}

void rel_template_suit::display() {
    std::cout << "templates: " << m_rel_templates.size() << "\n";
    for (unsigned i = 0; i < m_rel_templates.size(); i++) {
        std::cout << "template " << i << " : " << m_rel_templates[i].m_head->get_decl()->get_name() << " / " << m_rel_templates[i].m_head->get_decl()->get_arity() << "\n";
        std::cout << "template body : " << mk_pp(m_rel_templates[i].m_body, m_rel_manager) << "\n";
        std::cout << "template head : " << mk_pp(m_rel_templates[i].m_head, m_rel_manager) << "\n";
    }
    std::cout << "instances: " << m_rel_template_instances.size() << "\n";
    for (unsigned i = 0; i < m_rel_template_instances.size(); i++) {
        std::cout << "instance " << i << " : " << m_rel_template_instances[i].m_head->get_decl()->get_name() << " / " << m_rel_template_instances[i].m_head->get_decl()->get_arity() << "\n";
        std::cout << "instance body : " << mk_pp(m_rel_template_instances[i].m_body, m_rel_manager) << "\n";
        std::cout << "instance head : " << mk_pp(m_rel_template_instances[i].m_head, m_rel_manager) << "\n";

        expr_ref_vector inst_body_terms(m_rel_manager);
        get_conj_terms(m_rel_template_instances[i].m_body, inst_body_terms);
        std::cout << "inst_body_terms: " << inst_body_terms.size() << "\n";
        for (unsigned j = 0; j < inst_body_terms.size(); j++) {
            std::cout << "inst_body_terms : " << mk_pp(inst_body_terms.get(j), m_rel_manager) << "\n";
        }
    }

    std::cout << "orig templates: " << m_rel_templates_orig.size() << "\n";
    for (unsigned i = 0; i < m_rel_templates_orig.size(); i++) {
        std::cout << "orig template " << i << " : " << m_rel_templates_orig[i].m_head->get_decl()->get_name() << " / " << m_rel_templates_orig[i].m_head->get_decl()->get_arity() << "\n";
        std::cout << "orig template body : " << mk_pp(m_rel_templates_orig[i].m_body, m_rel_manager) << "\n";
        std::cout << "orig template head : " << mk_pp(m_rel_templates_orig[i].m_head, m_rel_manager) << "\n";
    }
}

void core_to_throw::display() {
    std::cout << "root_id: " << root_id << ", last_name: " << last_name << ", last_id: " << last_node_tid << ", last_ids: [";
    for (unsigned i = 0; i < last_node_ids.size(); i++) {
        std::cout << " " << last_node_ids.get(i);
    }
    std::cout << "], critical pos: " << pos << "\n";
    std::cout << "name_map: [";
    for (unsigned i = 0; i < name_map.size(); i++) {
        std::cout << " " << name_map.get(i).first << "-" << name_map.get(i).second.str();
    }
    std::cout << "]\n";
    std::cout << "core size: " << core.size() << "\n";
    display_core_tree(core);
}

void refine_pred_info::display() {
    std::cout << "pred: " << mk_pp(pred.get(), pred.m()) << ", pred_vars: [";
    for (unsigned i = 0; i < pred_vars.size(); i++) {
        std::cout << " " << mk_pp(pred_vars.get(i), pred.m());
    }
    std::cout << "]\n";
}

void refine_cand_info::display() {
    for (unsigned i = 0; i < m_allrels_info.size(); i++) {
        std::cout << "refine_cand_info: " << i << ": " << m_allrels_info.get(i).first.str() << " -[ ";
        for (unsigned j = 0; j < m_allrels_info.get(i).second.size(); j++) {
            std::cout << "usage " << j << " -[ ";
            for (unsigned k = 0; k < m_allrels_info.get(i).second.get(j).size(); k++) {
                std::cout << mk_pp(m_allrels_info.get(i).second.get(j).get(k), m) << " ";
            }
            std::cout << " ] ";
        }
        std::cout << " ] \n";
    }
}
