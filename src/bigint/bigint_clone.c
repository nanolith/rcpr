/**
 * \file bigint/bigint_clone.c
 *
 * \brief Clone a \ref bigint instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>

#include "bigint_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_bigint;
RCPR_IMPORT_bigint_internal;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(bigint);

/**
 * \brief Clone a \ref bigint instance.
 *
 * \param i         Pointer to the \ref bigint pointer to receive the new
 *                  resource on success.
 * \param a         The allocator to use for cloning this instance.
 * \param j         The \ref bigint instance to clone.
 *
 * \note The cloned \ref bigint is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling
 * \ref bigint_resource_handle on this \ref bigint instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p i must not reference a valid \ref bigint instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p j must reference a valid \ref bigint instance.
 *
 * \post
 *      - On success, \p i is set to a pointer to a valid \ref bigint instance,
 *        which is a \ref resource owned by the called that must be released.
 *      - On failure, \p i is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(bigint_clone)(
    RCPR_SYM(bigint)** i, RCPR_SYM(allocator)* a, const RCPR_SYM(bigint)* j)
{
    status retval, reclaim_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(prop_bigint_valid(j));

    /* attempt to allocate memory for the cloned bigint instacne. */
    bigint* tmp = NULL;
    retval =
        allocator_allocate(a, (void**)&tmp, sizeof(bigint));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* copy structure. */
    memcpy(tmp, j, sizeof(bigint));

    /* fix up some values. */
    tmp->a = a;
    /* force struct tag invariant to be false, since this is a new value. */
    #ifdef CBMC
    tmp->MODEL_STRUCT_TAG_REF(bigint) = 0;
    #endif

    /* attempt to allocate memory for the integer array. */
    native_int* int_bytes = NULL;
    retval =
        allocator_allocate(
            a, (void**)&int_bytes, sizeof(native_int) * tmp->length);
    if (STATUS_SUCCESS != retval)
    {
        goto free_bigint;
    }

    /* copy the bytes from the original bigint value. */
    memcpy(int_bytes, j->array, sizeof(native_int) * tmp->length); 

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(bigint), bigint);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(bigint), bigint);

    /* set the array. */
    tmp->array = int_bytes;

    /* set the returned bigint. */
    *i = tmp;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_bigint_valid(*i));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

free_bigint:
    reclaim_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS == retval)
        retval = reclaim_retval;

done:
    return retval;
}
