/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mcsat_default_solver.cpp

Abstract:

    MCSAT solver pre-configured with several tactics 
    and components.

Author:

    Leonardo de Moura (leonardo) 2012-12-13.

Revision History:

--*/
#include"mcsat_default_solver.h"
#include"simplify_tactic.h"
#include"nnf_tactic.h"

namespace mcsat {
    default_solver_factory::default_solver_factory() {
        add_tactic_after(alloc(simplify_tactic_factory));
        add_tactic_after(alloc(nnf_tactic_factory));
    }
    
    default_solver_factory::~default_solver_factory() {
    }
};
