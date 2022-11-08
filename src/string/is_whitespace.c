/**
 * \file string/is_whitespace.c
 *
 * \brief Check to see if the first character in a string is a whitespace.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/string.h>

/**
 * \brief Return true if the first character of a given string is a whitespace
 * character.
 *
 * \brief str           The string to check.
 *
 * \returns true if the character is a whitespace character and false otherwise.
 */
bool RCPR_SYM(is_whitespace)(const char* str)
{
    if (NULL == str || 0 == *str)
    {
        return false;
    }
    else
    {
        char ch = *str;

        switch (ch)
        {
            case '\t':
            case '\n':
            case '\v':
            case '\f':
            case '\r':
            case ' ':
                return true;

            default:
                return false;
        }
    }
}
