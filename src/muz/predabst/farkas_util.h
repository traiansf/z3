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

typedef std::pair<unsigned, symbol> name2symbol;
typedef std::map<unsigned, std::pair<std::pair<unsigned, vector<unsigned> >, vector<unsigned> > > core_tree;

struct core_to_throw {
    unsigned root_id;
    unsigned last_name;
    unsigned last_node_tid;
    vector<unsigned> last_node_ids;
    unsigned pos;
    vector<name2symbol> name_map;
    core_tree core;

    core_to_throw(unsigned in_root_id, unsigned in_last_name, unsigned in_last_node_tid, vector<unsigned> in_last_node_ids, unsigned in_pos,
                  vector<name2symbol> in_name_map, core_tree in_core) {
        root_id = in_root_id;
        last_name = in_last_name;
        last_node_tid = in_last_node_tid;
        last_node_ids = in_last_node_ids;
        pos = in_pos;
        name_map = in_name_map;
        core = in_core;
    }

    void display(std::ostream& out);
};

typedef std::map<unsigned, std::pair<expr_ref_vector, std::pair<expr_ref, expr_ref_vector> > > core_clauses;
typedef vector<std::pair<symbol, std::pair<expr_ref_vector, std::pair<expr_ref, expr_ref_vector> > > > core_clauses2;

struct refine_pred_info {
    expr_ref pred;
    expr_ref_vector pred_vars;

    refine_pred_info(expr_ref in_pred, expr_ref_vector in_pred_vars) : pred_vars(in_pred_vars), pred(in_pred) {}

    bool has_var(expr_ref arg) {
        return pred_vars.contains(arg);
    }

    void display(std::ostream& out);
};

struct refine_cand_info {

    typedef vector<std::pair<symbol, vector<expr_ref_vector> > > refine_cand_rels_info;

    refine_cand_rels_info m_allrels_info;
    ast_manager& m;

    refine_cand_info(ast_manager& in_m) : m(in_m) {}

    void insert(symbol sym, expr_ref_vector args);

    refine_cand_rels_info get_info() {
        return m_allrels_info;
    }

    void display(std::ostream& out);
};

void get_interpolant_pred(expr_ref_vector args, expr_ref_vector vars, vector<refine_pred_info> interpolants, expr_ref_vector& in_pred);

void get_conj_terms(expr_ref conj, expr_ref_vector& terms);

bool well_founded(expr_ref_vector vars, expr_ref& LHS, expr_ref& bound, expr_ref& decrease);

void well_founded_cs(expr_ref_vector vsws, expr_ref& bound, expr_ref& decrease);

expr_ref_vector get_all_pred_vars(expr_ref& fml);

bool solve_clauses2(core_clauses clauses, ast_manager& m, vector<refine_pred_info>& interpolants);

void mk_conj(expr_ref_vector terms, expr_ref& conj);

void mk_conj(expr_ref term1, expr_ref term2, expr_ref& conj);

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

    vector<symbol> m_names;

    expr_ref subst_template_body(expr_ref fml, vector<rel_template> rel_templates);
    expr_ref subst_template_body(expr_ref fml, vector<rel_template> rel_templates, expr_ref_vector& args);

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

    void process_template_extra(expr_ref_vector& t_params, expr_ref extras) {
        m_params.append(t_params);
        m_extras = extras;
    }

    void process_template(symbol head_name, rel_template aa, expr_ref_vector temp_subst) {
        m_rel_templates.push_back(aa);
        m_names.push_back(head_name);
        m_temp_subst.append(temp_subst);
    }

    void process_template_sk(rel_template aa) {
        m_rel_templates_orig.push_back(aa);
    }

    void init_template_instantiate();
    bool constrain_template(expr_ref fml);

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

    vector<symbol> get_names() {
        return  m_names;
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

    void display(std::ostream& out);
};

#endif /* _FARKAS_UTIL_H_ */
