/**
 * \file bigint/bigint_create_zero.c
 *
 * \brief Create a \ref bigint instance, set to zero.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>

#include "bigint_internal.h"

/* forward decls. */
MODEL_STRUCT_TAG_GLOBAL_EXTERN(bigint);

/**
 * \brief Create a \ref bigint instance of a given size.
 *
 * \param i             Pointer to the \ref bigint pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      list resource and to allocate new nodes.
 * \param size          The minimum size of this bigint in bits; the actual
 *                      representation might be larger to accomodate native
 *                      integer size.
 *
 * \note This \ref bigint is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref bigint_resource_handle on this \ref bigint instance.
 *
 * This value will be the bigint equivalent of zero on success.
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
 *
 * \post
 *      - On success, \p i is set to a pointer to a valid \ref bigint
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p i is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
bigint_create_zero(
    bigint** i, allocator* a, size_t size)
{
    status retval, reclaim_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != i);
    MODEL_ASSERT(prop_allocator_valid(a));

    /* compute the size in bytes based on the bit size. */
    size_t byte_size = size / 8;

    /* adjust this size to the nearest byte. */
    if (size % 8 > 0)
        ++byte_size;

    /* compute the size in single ints based on the byte size. */
    size_t int_size = byte_size / sizeof(native_single_int);

    /* adjust this size to the nearest native int size. */
    if (byte_size % sizeof(native_single_int) > 0)
        ++int_size;

    /* attempt to allocate memory for this bigint instance. */
    bigint* tmp = NULL;
    retval =
        allocator_allocate(a, (void**)&tmp, sizeof(bigint));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(bigint));

    /* attempt to allocate memory for the integer array. */
    native_double_int* int_bytes = NULL;
    retval =
        allocator_allocate(
            a, (void**)&int_bytes, int_size * sizeof(native_double_int));
    if (STATUS_SUCCESS != retval)
    {
        goto free_bigint;
    }

    /* clear these bytes (assign the value to zero). */
    memset(int_bytes, 0, int_size * sizeof(native_double_int));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(bigint), bigint);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(bigint), bigint);

    /* set the release method. */
    resource_init(&tmp->hdr, &bigint_release);

    /* set the allocator. */
    tmp->a = a;

    /* set the array and length. */
    tmp->length = int_size;
    tmp->array = int_bytes;

    /* set the returned bigint. */
    *i = tmp;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_bigint_valid(*i));

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
