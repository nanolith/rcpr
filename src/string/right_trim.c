/**
 * \file string/right_trim.c
 *
 * \brief Perform a right trim of the given string.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

/**
 * \brief Perform a right trim of the given string.
 *
 * Remove all whitespace on the right-hand side of the string -- from the ASCII
 * zero to the first non-whitespace character -- are trimmed.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to modify.
 */
void RCPR_SYM(right_trim)(char* str)
{
    char* tmp = str;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != str);

    /* iterate through the string to reach the end of the string. */
    while (*tmp != 0)
    {
        ++tmp;
    }

    /* if tmp != str, decrement tmp so we are looking at the last character. */
    if (tmp != str)
    {
        --tmp;
    }

    /* iterate back from the end of the string to either the
     * first-non-whitespace character OR the beginning of the string. */
    while (tmp != str && rcpr_is_whitespace(*tmp))
    {
        --tmp;
    }

    /* there are four possibilities. */
    
    /* tmp == str and... */
    if (tmp == str)
    {
        /* this is a blank string, and we're done. */
        if (*tmp == 0)
        {
            return;
        }

        /* tmp is a space, and we've trimmed the whole string. */
        if (rcpr_is_whitespace(*tmp))
        {
            *tmp = 0;
        }
        /* tmp is NOT as space, so trim one past tmp. */
        else
        {
            tmp[1] = 0;
        }
    }
    /* tmp != str, and therefore, the last space was at tmp+1. */
    else
    {
        tmp[1] = 0;
    }
}
