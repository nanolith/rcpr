/**
 * \file string/right_trim.c
 *
 * \brief Perform a trim (left and right trim) of the given string.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

/**
 * \brief Perform a trim of the given string.
 *
 * Remove all whitespace on the left-hand and right-hand sides of the string.
 * All whitespace from the beginning of the string to the first non-whitespace
 * character and all whitespace from the end of the string to the last
 * non-whitespace character are removed.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to modify.
 */
void RCPR_SYM(trim)(char* str)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != str);

    /* a trim is a right trim followed by a left trim. */
    rcpr_right_trim(str);
    rcpr_left_trim(str);
}
