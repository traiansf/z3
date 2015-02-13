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

bool well_founded(expr_ref_vector const& vars, expr_ref const& LHS, expr_ref& bound, expr_ref& decrease);

expr_ref well_founded_cs(expr_ref_vector const& vsws);

vector<refine_pred_info> solve_clauses(core_clauses const& clauses, ast_manager& m);

struct rel_template {
    app* m_head;
    expr_ref m_body;

    rel_template(app* head, expr_ref const& body) :
        m_head(head),
        m_body(body) {}
};

class rel_template_suit {
    ast_manager& m_rel_manager;
    var_subst m_var_subst;

    vector<func_decl*> m_names;
    vector<rel_template> m_rel_templates_orig;
    vector<rel_template> m_rel_templates;
    vector<rel_template> m_rel_template_instances;

    expr_ref_vector m_params;
    expr_ref m_extras;
    expr_ref m_extra_sol;
    expr_ref m_acc;

    model_ref m_modref;

    expr_ref_vector subst_template_body(expr_ref_vector const& fmls, vector<rel_template> const& rel_templates, expr_ref_vector& args_coll);
    expr_ref subst_template_body(expr_ref const& fml, vector<rel_template> const& rel_templates, expr_ref_vector& args);

public:

    rel_template_suit(ast_manager& m) :
        m_rel_manager(m),
        m_var_subst(m_rel_manager, false),
        m_params(m_rel_manager),
        m_extras(m_rel_manager),
        m_extra_sol(m_rel_manager),
        m_acc(expr_ref(m_rel_manager.mk_true(), m_rel_manager)) {}

    void process_template_extra(expr_ref_vector& t_params, expr_ref const& extras) {
        CASSERT("predabst", m_params.size() == 0);
        m_params.append(t_params);
        CASSERT("predabst", !m_extras);
        m_extras = extras;
    }

    void process_template(func_decl* head_name, rel_template const& orig_temp, rel_template const& temp) {
        m_names.push_back(head_name);
        m_rel_templates_orig.push_back(orig_temp);
        m_rel_templates.push_back(temp);
    }

    void init_template_instantiate();
    bool constrain_template(expr_ref const& fml);

    vector<func_decl*> const& get_names() {
        return m_names;
    }

    vector<rel_template> const& get_orig_templates() const {
        return m_rel_templates_orig;
    }

    vector<rel_template> const& get_templates() const {
        return m_rel_templates;
    }

    vector<rel_template> const& get_template_instances() const {
        return m_rel_template_instances;
    }

    void rel_template_suit::get_orig_template(unsigned i, expr_ref& body, expr_ref_vector& vars) {
        rel_template const& orig = m_rel_templates_orig[i];
        body = orig.m_body;
        vars.append(orig.m_head->get_num_args(), orig.m_head->get_args());
    }

    void rel_template_suit::get_template_instance(unsigned i, expr_ref& body, expr_ref_vector& vars) {
        rel_template const& instance = m_rel_template_instances[i];
        body = instance.m_body;
        vars.append(instance.m_head->get_num_args(), instance.m_head->get_args());
    }

    expr_ref_vector const& get_params() {
        return m_params;
    }

    model_ref get_modref() {
        return m_modref;
    }

    void display(std::ostream& out) const;
};

#endif /* _FARKAS_UTIL_H_ */
