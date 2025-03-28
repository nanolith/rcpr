/**
 * \file string/split.c
 *
 * \brief Shadow implementation of split.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

static bool nondet_success();

status FN_DECL_MUST_CHECK
RCPR_SYM(split)(const char** lhs, const char** rhs, char* str, int delim)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(split), lhs, rhs, str, delim);

    const char* tmp;
    int retval;

    if (nondet_success())
    {
        *lhs = *rhs = str;
        retval = STATUS_SUCCESS;
        goto done;
    }
    else
    {
        *lhs = *rhs = NULL;
        retval = ERROR_STRING_END_OF_INPUT;
        goto done;
    }

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(split), retval, lhs, rhs);

    return retval;
}
