/**
 * \file string/ends_with.c
 *
 * \brief shadow impl of ends_with.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

static bool nondet_bool();

bool RCPR_SYM(ends_with)(const char* str, int ch)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(ends_with), str, ch);

    bool retval = nondet_bool();

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(ends_with), retval);

    return retval;
}
