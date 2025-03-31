/**
 * \file string/strdup.c
 *
 * \brief strdup shadow impl.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_allocator;

status FN_DECL_MUST_CHECK
RCPR_SYM(strdup)(
    char** output, RCPR_SYM(allocator)* alloc, const char* input)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(strdup), output, alloc, input);

    status retval;
    char* tmp;

    /* get the length of the input string. */
    size_t len = strlen(input);

    /* allocate len + 1 bytes. */
    retval = allocator_allocate(alloc, (void**)&tmp, len + 1);
    if (STATUS_SUCCESS != retval)
    {
        *output = NULL;
        goto done;
    }

    /* randomize this string. */
    __CPROVER_havoc_object(tmp);

    /* ASCIIZ this new string. */
    tmp[len] = 0;

    /* force this string to be recognized as one by the model checker. */
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(tmp));

    /* success. */
    *output = tmp;
    retval = STATUS_SUCCESS;
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(strdup), retval, output);

    return retval;
}
