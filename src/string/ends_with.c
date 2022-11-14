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
    (void)str;
    (void)ch;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != str);

    /* can't match an empty string. */
    if (0 == *str)
    {
        return false;
    }

    /* skip to the end of the string. */
    while (0 != *str) ++str;

    /* move back by one. */
    --str;

    /* compare the values. */
    return *str == ch;
}
