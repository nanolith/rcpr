/**
 * \file string/chomp.c
 *
 * \brief Shadow impl of chomp.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

void RCPR_SYM(chomp)(char* str)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(chomp), str);

    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(chomp), str);
}
