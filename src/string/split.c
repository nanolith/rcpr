/**
 * \file string/split.c
 *
 * \brief Split a string into two halves based on the first occurrence of a
 * given delimiter.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

/**
 * \brief Split a string into two halves based on the first occurrence of the
 * given character.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param lhs           Pointer to the character pointer to be set to the
 *                      left-hand side of the split.
 * \param rhs           Pointer to the character pointer to be set to the
 *                      right-hand side of the split.
 * \param str           The string to split.
 * \param delim         The delimiter character on which the string is split.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_STRING_END_OF_INPUT if the delimiter could not be found.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(split)(const char** lhs, const char** rhs, char* str, int delim)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(split), lhs, rhs, str, delim);

    const char* tmp;
    int retval;

    /* the left-hand-side starts at str. */
    tmp = str;

    /* scroll for the first occurrence of delim. */
    for (int ch = *str; ch != 0 && ch != delim; ch = *(++str));

    /* if str is ASCIIZ, then delim wasn't found. */
    if (0 == *str)
    {
        retval = ERROR_STRING_END_OF_INPUT;
        *lhs = NULL;
        *rhs = NULL;
        goto done;
    }
    /* otherwise, set str to ASCIIZ and set rhs to str+1. */
    else
    {
        *lhs = tmp;
        *rhs = str + 1;
        *str = 0;
        retval = STATUS_SUCCESS;
    }

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(split), retval, lhs, rhs);

    return retval;
}
