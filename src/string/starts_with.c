/**
 * \file string/starts_with.c
 *
 * \brief Return true if the given string starts with the given substring.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

/**
 * \brief Return true if the given string starts with the given substring.
 *
 * \param str           The string to check.
 * \param substr        The substring to match at the beginning of \p str.
 *
 * \returns true if \p str starts with \p substr and false otherwise.
 */
bool RCPR_SYM(starts_with)(const char* str, const char* substr)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != str);
    RCPR_MODEL_ASSERT(NULL != substr);

    /* if substr is NULL, then the result is always true. */
    if (NULL == substr)
    {
        return true;
    }

    /* substr must be not NULL; if str is NULL, then the result is false. */
    if (NULL == str)
    {
        return false;
    }

    /* get the sizes of the strings. */
    size_t str_size = strlen(str);
    size_t substr_size = strlen(substr);

    /* if the string size is less than the substring size, then they can't
     * match. */
    if (str_size < substr_size)
    {
        return false;
    }

    /* does str start with substr? */
    if (!memcmp(str, substr, substr_size))
    {
        return true;
    }

    /* str doesn't start with substr. */
    return false;
}
