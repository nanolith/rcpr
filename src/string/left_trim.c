/**
 * \file string/left_trim.c
 *
 * \brief Perform a left trim of the given string.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

/**
 * \brief Perform a left trim of the given string.
 *
 * Remove all whitespace on the left-hand side of the string up to the first
 * non-whitespace character.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to modify.
 */
void RCPR_SYM(left_trim)(char* str)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(left_trim), str);

    char* tmp = str;

    /* iterate through the string while whitespace is detected. */
    while (rcpr_is_whitespace(*tmp))
    {
        ++tmp;
    }

    /* at this point, we have either encountered a non-whitespace character or
     * the end of the string. From this position, scroll to the end of the
     * string, which could be this position. */
    char* eos = tmp;
    while (0 != *eos)
    {
        ++eos;
    }

    /* compute the size of the modified string, including the ASCII zero. */
    size_t strsize = (eos - tmp) + 1;

    /* move the trimmed string to the start of this string. */
    memmove(str, tmp, strsize);

    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(left_trim), str);
}
