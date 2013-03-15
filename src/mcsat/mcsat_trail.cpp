/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_trail.cpp

Abstract:

    Trail is the main component of the MCSat Kernel.
    It is also the communication bus for all MCSat components.
    
    For more details see the paper:
    "A model-constructing satisfiability calculus", VMCAI'13

Author:

    Leonardo de Moura (leonardo) 2012-12-14

Revision History:

*/
#include"mcsat_trail.h"

namespace mcsat {

    bool trail::is_decision() const {
        return false;
    }

    bool trail::is_assumption() const {
        return false;
    }

    literal trail::lit() const {
        return null_literal;
    }
    
    trail_kind propagated_literal::kind() const {
        return k_propagated_literal;
    }

    literal propagated_literal::lit() const {
        return m_literal;
    }

    trail_kind propagated_eq::kind() const {
        return k_propagated_eq;
    }

    trail_kind propagated_diseq::kind() const {
        return k_propagated_diseq;
    }

    bool decision::is_decision() const {
        return true;
    }

    literal decided_literal::lit() const {
        return m_literal;
    }

    trail_kind decided_literal::kind() const {
        return k_decided_literal;
    }
    
    bool assumed_literal::is_assumption() const {
        return true;
    }

    trail_kind assumed_literal::kind() const {
        return k_assumed_literal;
    }

    trail_kind model_assignment::kind() const {
        return k_model_assignment;
    }

    trail_kind assign_interpretation::kind() const {
        return k_assign_interp;
    }

    trail_kind assign_func_interpretation::kind() const {
        return k_assign_func_interp;
    }

    trail_kind conflict::kind() const {
        return k_conflict;
    }

    trail_manager::trail_manager() {
        m_next_kind = k_first_extra;
    }
    
    trail_manager::~trail_manager() {
    }
    
    trail_kind trail_manager::mk_kind() {
        trail_kind r = m_next_kind;
        m_next_kind++;
        return r;
    }

    void trail_manager::push() {
        m_region.push_scope();
    }

    void trail_manager::pop(unsigned num_scopes) {
        m_region.pop_scope(num_scopes);
    }

    trail_stack::trail_stack() {
    }
    
    trail_stack::~trail_stack() {
    }

    void trail_stack::push() {
        DEBUG_CODE({
                for (unsigned i = 0; i < m_plugin_qhead.size(); i++) {
                    SASSERT(m_plugin_qhead[i] == m_stack.size());
                }
            });
        m_scopes.push_back(m_stack.size());
    }

    void trail_stack::pop(unsigned num_scopes) {
        SASSERT(num_scopes <= m_scopes.size());
        unsigned new_lvl    = m_scopes.size() - num_scopes;
        unsigned old_sz     = m_scopes[new_lvl];
        m_stack.shrink(old_sz);
        unsigned sz = m_plugin_qhead.size();
        for (unsigned i = 0; i < sz; i++) {
            m_plugin_qhead[i] = old_sz;
        }
        m_scopes.shrink(new_lvl);
    }

    void trail_stack::push_back(trail * t) {
        m_stack.push_back(t);
    }

    trail * trail_stack::next(unsigned i) {
        if (m_plugin_qhead[i] == m_stack.size())
            return 0;
        trail * t = m_stack[m_plugin_qhead[i]];
        m_plugin_qhead[i]++;
        return t;
    }

    bool trail_stack::fully_propagated() const {
        unsigned sz = m_plugin_qhead.size();
        for (unsigned i = 0; i < sz; i++) {
            if (m_plugin_qhead[i] < m_stack.size())
                return false;
        }
        return true;
    }

};

