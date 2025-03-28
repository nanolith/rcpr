/**
 * \file string/chomp.c
 *
 * \brief Chomp a character off of the end of a string.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

/**
 * \brief Chomp a character off of the end of a string.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to chomp.
 */
void RCPR_SYM(chomp)(char* str)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(chomp), str);

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != str);

    /* if the string is empty, we're done. */
    if (0 == *str)
    {
        goto done;
    }

    /* skip to the end of the string. */
    while (0 != *str) ++str;

    /* move back by one. */
    --str;

    /* set this character to ASCIIZ. */
    *str = 0;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(chomp), str);
}
