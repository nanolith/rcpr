/**
 * \file models/shadow/string/trim.c
 *
 * \brief Shadow implementation of trim.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

void RCPR_SYM(trim)(char* str)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(left_trim), str);

    RCPR_MODEL_ASSUME(!rcpr_is_whitespace(str[0]));

    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(left_trim), str);
}
