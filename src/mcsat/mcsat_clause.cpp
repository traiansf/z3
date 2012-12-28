/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_clause.h

Abstract:

    MCSAT clause

Author:

    Leonardo de Moura (leonardo) 2012-12-27.

Revision History:

--*/
#include"mcsat_clause.h"
#include"small_object_allocator.h"

namespace mcsat {

    static node_approx_set mk_approx(unsigned num, literal const * lits) {
        node_approx_set r;
        for (unsigned i = 0; i < num; i++) 
            r.insert(lits[i].var());
        return r;
    }

    size_t clause::get_obj_size(unsigned num_lits) { 
        return sizeof(clause) + num_lits * sizeof(literal); 
    }

    clause::clause(unsigned id, unsigned sz, literal const * lits, bool learned, proof * pr):
        m_id(id),
        m_size(sz),
        m_approx(mk_approx(sz, lits)),
        m_used(false),
        m_learned(learned),
        m_reinit_stack(false),
        m_mark(false),
        m_pr(pr) {
        for (unsigned i = 0; i < sz; i++)
            m_lits[i] = lits[i];
    }

    bool clause::contains(literal l) const {
        for (unsigned i = 0; i < size(); i++)
            if (m_lits[i] == l)
                return true;
        return false;
    }

    bool clause::contains(node v) const {
        for (unsigned i = 0; i < size(); i++)
            if (m_lits[i].var() == v)
                return true;
        return false;
    }

    struct clause_manager::imp {
        region                 m_region;    // for main and auxiliary clauses.
        small_object_allocator m_allocator; // for lemmas.
        id_gen                 m_id_gen;
        ptr_vector<clause>     m_clauses;
        ptr_vector<clause>     m_lemmas;
        unsigned_vector        m_base_scopes; 
        unsigned_vector        m_scopes;
        imp():
            m_allocator("mcsat_clause_manager") {}

        void del_lemma(clause * c) {
            m_id_gen.recycle(c->id());
            size_t obj_sz = clause::get_obj_size(c->size());
            c->~clause();
            m_allocator.deallocate(obj_sz, c);
        }

        void del_clause(clause * c) {
            m_id_gen.recycle(c->id());
            c->~clause();
        }

        clause * mk(unsigned sz, literal const * lits, bool learned, proof * pr) {
            unsigned id = m_id_gen.mk();
            size_t obj_sz = clause::get_obj_size(sz);
            void * mem;
            if (learned)
                mem = m_allocator.allocate(obj_sz);
            else
                mem = m_region.allocate(obj_sz);
            clause * cls = new (mem) clause(id, sz, lits, learned, pr);
            if (learned)
                m_lemmas.push_back(cls);
            else
                m_clauses.push_back(cls);
            return cls;
        }

        void push(bool user) {
            SASSERT(user || m_scopes.size() == m_base_scopes.size());
            SASSERT(m_scopes.size() >= m_base_scopes.size());
            m_scopes.push_back(m_clauses.size());
            if (user)
                m_base_scopes.push_back(m_lemmas.size());
        }
        
        void restore_clauses(unsigned old_sz) {
            unsigned sz = m_clauses.size();
            SASSERT(old_sz <= sz);
            for (unsigned i = old_sz; i < sz; i++) {
                clause * c = m_clauses[i];
                del_clause(c);
            }
            m_clauses.shrink(old_sz);
        }

        void restore_lemmas(unsigned old_sz) {
            unsigned sz = m_lemmas.size();
            SASSERT(old_sz <= sz);
            for (unsigned i = old_sz; i < sz; i++) {
                clause * c = m_lemmas[i];
                del_lemma(c);
            }
            m_lemmas.shrink(old_sz);
        }
        
        void pop(unsigned num_scopes, bool user) {
            SASSERT(user || m_scopes.size() == m_base_scopes.size());
            SASSERT(m_scopes.size() >= m_base_scopes.size());
            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl    = m_scopes.size() - num_scopes;
            unsigned old_sz     = m_scopes[new_lvl];
            restore_clauses(old_sz);
            m_scopes.shrink(new_lvl);
            if (user) {
                SASSERT(num_scopes <= m_base_scopes.size());
                unsigned new_lvl    = m_base_scopes.size() - num_scopes;
                unsigned old_sz     = m_base_scopes[new_lvl];
                restore_lemmas(old_sz);
                m_base_scopes.shrink(new_lvl);
            }
        }
    };

    clause_manager::clause_manager() {
        m_imp = alloc(imp);
    }

    clause_manager::~clause_manager() {
        dealloc(m_imp);
    }
    
    void clause_manager::push(bool user) {
        m_imp->push(user);
    }

    void clause_manager::pop(unsigned num_scopes, bool user) {
        m_imp->pop(num_scopes, user);
    }

    clause * clause_manager::mk(unsigned sz, literal const * lits, proof * pr) {
        return m_imp->mk(sz, lits, false, pr);
    }

    clause * clause_manager::mk_lemma(unsigned sz, literal const * lits, proof * pr) {
        return m_imp->mk(sz, lits, true, pr);
    }

    clause_manager::iterator clause_manager::begin_lemmas() const {
        unsigned begin = m_imp->m_base_scopes.empty() ? 0 : m_imp->m_base_scopes.back();
        return m_imp->m_lemmas.begin() + begin;
    }

    clause_manager::iterator clause_manager::end_lemmas() const {
        return m_imp->m_lemmas.end();
    }

    void clause_manager::gc(ptr_vector<clause> const & to_delete) {
        DEBUG_CODE({
                iterator it  = begin_lemmas();
                iterator end = end_lemmas();
                for (; it != end; ++it) {
                    SASSERT(!(*it)->is_marked());
                }
            });

        iterator it  = to_delete.begin();
        iterator end = to_delete.end();
        for (; it != end; ++it) {
            SASSERT(!(*it)->is_marked());
            (*it)->mark();
        }
        
        DEBUG_CODE({
                unsigned num_marked = 0;
                iterator it  = begin_lemmas();
                iterator end = end_lemmas();
                for (; it != end; ++it) {
                    if ((*it)->is_marked())
                        num_marked++;
                }
                SASSERT(to_delete.size() == num_marked);
            });

        unsigned _begin = m_imp->m_base_scopes.empty() ? 0 : m_imp->m_base_scopes.back();
        unsigned _end   = m_imp->m_lemmas.size();
        SASSERT(_begin <= _end);
        unsigned j     = _begin;
        for (unsigned i = _begin; i < _end; i++) {
            clause * c = m_imp->m_lemmas[i];
            SASSERT(c->is_learned());
            if (c->is_marked()) {
                c->reset_mark();
                m_imp->del_lemma(c);
            }
            else {
                m_imp->m_lemmas[j] = c;
                j++;
            }
        }
        m_imp->m_lemmas.shrink(j);
    }


};
