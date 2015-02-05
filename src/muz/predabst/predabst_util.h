/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    predabst_util.h

Abstract:

    Miscellaneous utilities for use by predabst.

Author:

    James Lingard (jchl) 2015-02-05.

Revision History:

--*/
#ifndef _PREDABST_UTIL_H_
#define _PREDABST_UTIL_H_

#include "ast.h"

expr_ref_vector get_conj_terms(expr_ref const& conj);

expr_ref mk_disj(expr_ref_vector const& terms);

expr_ref mk_conj(expr_ref_vector const& terms);

expr_ref mk_conj(expr_ref const& term1, expr_ref const& term2);

expr* replace_pred(expr_ref_vector const& args, expr_ref_vector const& vars, expr* e);

expr_ref neg_and_2dnf(expr_ref const& fml);

#endif /* _PREDABST_UTIL_H */
