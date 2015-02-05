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

#include "model.h"
#include "var_subst.h"
#include <map>

typedef std::map<unsigned, std::pair<expr_ref_vector, std::pair<expr_ref, expr_ref_vector> > > core_clauses;
typedef vector<std::pair<func_decl*, std::pair<expr_ref_vector, std::pair<expr_ref, expr_ref_vector> > > > core_clauses2;

struct refine_pred_info {
    expr_ref        m_pred;
    expr_ref_vector m_pred_vars;

    refine_pred_info(expr_ref const& pred, expr_ref_vector const& pred_vars) :
        m_pred(pred),
        m_pred_vars(pred_vars) {}

    bool has_var(expr_ref const& arg) const {
        return m_pred_vars.contains(arg);
    }

    void display(std::ostream& out) const;
};

bool well_founded(expr_ref_vector const& vars, expr_ref const& LHS, expr_ref bound, expr_ref decrease);

void well_founded_cs(expr_ref_vector const& vsws, expr_ref bound, expr_ref decrease);

vector<refine_pred_info> solve_clauses(core_clauses const& clauses, ast_manager& m);

struct rel_template {
    app* m_head;
    expr_ref m_body;

    rel_template(app* head, expr_ref body) : m_head(head), m_body(body) {
    }
};

class rel_template_suit {

    ast_manager& m_rel_manager;

    vector<rel_template> m_rel_templates;
    vector<rel_template> m_rel_templates_orig;
    vector<rel_template> m_rel_template_instances;

    expr_ref_vector m_params;
    expr_ref m_extras;
    expr_ref m_extra_sol;
    expr_ref m_acc;

    vector<func_decl*> m_names;

    expr_ref subst_template_body(expr_ref const& fml, vector<rel_template> const& rel_templates);
    expr_ref subst_template_body(expr_ref const& fml, vector<rel_template> const& rel_templates, expr_ref_vector& args);

    var_subst m_var_subst;
    expr_ref_vector m_extra_subst;
    expr_ref_vector m_temp_subst;

    model_ref m_modref;

public:

    rel_template_suit(ast_manager& m) : m_rel_manager(m),
        m_extras(m_rel_manager),
        m_extra_sol(m_rel_manager),
        m_acc(expr_ref(m_rel_manager.mk_true(), m_rel_manager)),
        m_params(m_rel_manager),
        m_var_subst(m_rel_manager, false),
        m_extra_subst(m_rel_manager),
        m_temp_subst(m_rel_manager) {
    }

    void process_template_extra(expr_ref_vector& t_params, expr_ref const& extras) {
        m_params.append(t_params);
        m_extras = extras;
    }

    void process_template(func_decl* head_name, rel_template const& aa, expr_ref_vector const& temp_subst) {
        m_rel_templates.push_back(aa);
        m_names.push_back(head_name);
        m_temp_subst.append(temp_subst);
    }

    void process_template_sk(rel_template const& aa) {
        m_rel_templates_orig.push_back(aa);
    }

    void init_template_instantiate();
    bool constrain_template(expr_ref const& fml);

    vector<rel_template> get_template_instances() {
        return m_rel_template_instances;
    }

    vector<rel_template> get_templates() {
        return m_rel_templates;
    }

    bool get_orig_template(app* in_head, expr_ref& body);

    vector<rel_template> get_orig_templates() {
        return m_rel_templates_orig;
    }

    bool get_instance(app* head, expr_ref& body, expr_ref_vector& vars);

    unsigned get_params_count() {
        return m_params.size();
    }

    expr_ref_vector get_params() {
        return m_params;
    }

    expr_ref_vector get_temp_subst() {
        return m_temp_subst;
    }

    vector<func_decl*> get_names() {
        return m_names;
    }

    ast_manager& get_rel_manager() {
        return m_rel_manager;
    }

    expr_ref get_extras() {
        return m_extras;
    }

    model_ref get_modref() {
        return m_modref;
    }

    void reset() {
        m_rel_template_instances.reset();
    }

    void display(std::ostream& out) const;
};

#endif /* _FARKAS_UTIL_H_ */
