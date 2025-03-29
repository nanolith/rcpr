/**
 * \file string/starts_with.c
 *
 * \brief Shadow impl of starts_with.
 *
 * \copyright 2023-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

static bool nondet_bool();

bool RCPR_SYM(starts_with)(const char* str, const char* substr)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(starts_with), str, substr);

    bool retval = nondet_bool();

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(starts_with), retval);

    return retval;
}
