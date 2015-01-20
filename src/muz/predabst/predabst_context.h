/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_context.h

Abstract:

    Predicate abstraction context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26
    Modified by Andrey Rybalchenko (rybal) 2014-3-7.

Revision History:

--*/
#ifndef _PREDABST_CONTEXT_H_
#define _PREDABST_CONTEXT_H_

#include "ast.h"
#include "lbool.h"
#include "statistics.h"
#include "dl_engine_base.h"

namespace datalog {
    class context;

    class predabst : public datalog::engine_base {
        class imp;
        imp* m_imp;
    public:
        predabst(context& ctx);
        ~predabst();
        virtual lbool query(expr* query);
        virtual void cancel();
        virtual void cleanup();
        virtual void reset_statistics();
        virtual void collect_statistics(statistics& st) const;
        virtual void display_certificate(std::ostream& out) const;
        virtual expr_ref get_answer();
        virtual model_ref get_model();
    };
};

template<class T>
inline std::ostream& operator<<(std::ostream&, const vector<T>&);

#endif
