/**
 * \file string/strdup.c
 *
 * \brief Duplicate a string using the given RCPR allocator instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_allocator;

/**
 * \brief Duplicate a string, creating a duplicate backed by the given allocator
 * instance.
 *
 * On success, the string is duplicated, and the output string pointer is
 * updated with the duplicate string. This string is owned by the caller, and
 * when it is no longer needed, it must be reclaimed using the same allocator
 * used to in this operation.
 *
 * \param output        Pointer to receive the duplicated string on success.
 * \param alloc         The allocator instance to use for this operation.
 * \param input         Pointer to the string to be duplicated in this
 *                      operation.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(strdup)(
    char** output, RCPR_SYM(allocator)* alloc, const char* input)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(strdup), output, alloc, input);

    status retval;
    char* tmp;

    /* runtime parameter sanity checks. */
    if (NULL == output || NULL == alloc || NULL == input)
    {
        if (NULL != output)
        {
            *output = NULL;
        }
        retval = ERROR_STRING_INVALID_PARAMETER;
        goto done;
    }

    /* get the length of the input string. */
    size_t len = strlen(input);

    /* allocate len + 1 bytes. */
    retval = allocator_allocate(alloc, (void**)&tmp, len + 1);
    if (STATUS_SUCCESS != retval)
    {
        *output = NULL;
        goto done;
    }

    /* copy the input to this memory. */
    memcpy(tmp, input, len);

    /* ASCIIZ this new string. */
    tmp[len] = 0;

    /* success. */
    *output = tmp;
    retval = STATUS_SUCCESS;
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(strdup), retval, output);

    return retval;
}
