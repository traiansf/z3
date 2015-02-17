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

bool interpolate(expr_ref_vector const& vars, expr_ref fmlA, expr_ref fmlB, expr_ref& fmlQ_sol);

bool well_founded(expr_ref_vector const& vars, expr_ref const& LHS, expr_ref& bound, expr_ref& decrease);

expr_ref well_founded_cs(expr_ref_vector const& vsws);

struct rel_template {
    app_ref m_head;
    expr_ref m_body;

    rel_template(app_ref const& head, expr_ref const& body) :
        m_head(head),
        m_body(body) {}
};

class rel_template_suit {
    ast_manager& m;
    mutable var_subst m_var_subst;

    expr_ref_vector m_params;
    expr_ref m_extras;

    vector<rel_template> m_rel_templates_orig;
    vector<rel_template> m_rel_templates;
    vector<rel_template> m_rel_template_instances;

    expr_ref m_acc;

    model_ref m_modref;

    expr_ref_vector subst_template_body(expr_ref_vector const& fmls, vector<rel_template> const& rel_templates, expr_ref_vector& args_coll) const;
    expr_ref subst_template_body(expr_ref const& fml, vector<rel_template> const& rel_templates, expr_ref_vector& args) const;

    bool has_template(func_decl* fdecl) const {
        for (unsigned i = 0; i < m_rel_templates.size(); ++i) {
            if (m_rel_templates[i].m_head->get_decl() == fdecl) {
                return true;
            }
        }
        return false;
    }

    bool instantiate_templates(expr_ref const& constraint);

public:

    rel_template_suit(ast_manager& m) :
        m(m),
        m_var_subst(m, false),
        m_params(m),
        m_extras(m),
        m_acc(expr_ref(m.mk_true(), m)) {}

    void process_template_extra(expr_ref_vector& t_params, expr_ref const& extras) {
        CASSERT("predabst", m_params.size() == 0);
        m_params.append(t_params);
        CASSERT("predabst", !m_extras);
        m_extras = extras;
    }

    void process_template(rel_template const& orig_temp, rel_template const& temp) {
        m_rel_templates_orig.push_back(orig_temp);
        m_rel_templates.push_back(temp);
    }

    bool instantiate_templates();

    void constrain_templates(expr_ref const& fml) {
        m_acc = mk_conj(fml, m_acc);
    }

    unsigned get_num_templates() const {
        return m_rel_templates.size();
    }

    rel_template const& get_orig_template(unsigned i) const {
        return m_rel_templates_orig.get(i);
    }

    rel_template const& get_template(unsigned i) const {
        return m_rel_templates.get(i);
    }

    rel_template const& get_template_instance(unsigned i) const {
        return m_rel_template_instances.get(i);
    }

    void rel_template_suit::get_orig_template(unsigned i, expr_ref& body, expr_ref_vector& vars) const {
        rel_template const& orig = m_rel_templates_orig[i];
        body = orig.m_body;
        vars.append(orig.m_head->get_num_args(), orig.m_head->get_args());
    }

    void rel_template_suit::get_template_instance(unsigned i, expr_ref& body, expr_ref_vector& vars) const {
        rel_template const& instance = m_rel_template_instances[i];
        body = instance.m_body;
        vars.append(instance.m_head->get_num_args(), instance.m_head->get_args());
    }

    expr_ref_vector const& get_params() const {
        return m_params;
    }

    model_ref get_modref() {
        return m_modref;
    }

    void display(std::ostream& out) const;
};

#endif /* _FARKAS_UTIL_H_ */
