/**
 * \file string/vstrcat.c
 *
 * \brief Concatenate multiple strings into a single allocated string field.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_allocator;

/**
 * \brief Varargs form of \ref strcatv.
 *
 * On success, the string is allocated using the provided allocator. The caller
 * owns this string and must reclaim it using the same allocator instance when
 * it is no longer needed.
 *
 * \param output        Pointer to receive the concatenated string on success.
 * \param alloc         The allocator to use for this instance.
 * \param string1       The first string to concatenate.
 * \param args          The varargs list (NULL terminated) of remaining strings
 *                      to concatenate.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(vstrcat)(
    char** output, RCPR_SYM(allocator)* alloc, const char* string1,
    va_list args)
{
    status retval;
    va_list count_list;
    size_t size = 1U;
    const char* arg = string1;
    char* tmp = NULL;

    va_copy(count_list, args);

    while (NULL != arg)
    {
        size += strlen(arg);
        arg = va_arg(count_list, const char*);
    }

    /* allocate memory for the concatenated string. */
    retval = allocator_allocate(alloc, (void**)&tmp, size);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* copy all strings into this string. */
    size_t offset = 0U;
    arg = string1;
    while (NULL != arg)
    {
        size_t argsize = strlen(arg);
        memcpy(tmp + offset, arg, argsize);
        offset += argsize;
        arg = va_arg(args, const char*);
    }

    /* ASCIIZ this string. */
    tmp[offset] = 0;

    /* success. */
    *output = tmp;
    retval = STATUS_SUCCESS;
    goto done;

done:
    va_end(count_list);
    return retval;
}
