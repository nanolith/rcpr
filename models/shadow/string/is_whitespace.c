/**
 * \file string/is_whitespace.c
 *
 * \brief Return true if the given character is a whitespace character.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/string.h>

bool RCPR_SYM(is_whitespace)(int ch)
{
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
