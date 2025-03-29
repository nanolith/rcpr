/**
 * \file string/ends_with.c
 *
 * \brief Return true if the given string ends with the given character.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

/**
 * \brief Return true if the given string ends with the given character.
 *
 * \param str           The string to check.
 * \param ch            The character to check.
 *
 * \returns true if the string ends with the given character and false
 * otherwise.
 */
bool RCPR_SYM(ends_with)(const char* str, int ch)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(ends_with), str, ch);

    bool retval;

    /* can't match an empty string. */
    if (0 == *str)
    {
        retval = false;
        goto done;
    }

    /* skip to the end of the string. */
    while (0 != *str) ++str;

    /* move back by one. */
    --str;

    /* compare the values. */
    retval = (*str == ch);
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(ends_with), retval);

    return retval;
}
