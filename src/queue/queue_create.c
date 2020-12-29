/**
 * \file queue/queue_create.c
 *
 * \brief Create a \ref queue instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "queue_internal.h"

/* forward decls. */
static status queue_release(resource*);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(queue);

/**
 * \brief Create a \ref queue instance.
 *
 * \param q             Pointer to the \ref queue pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      queue resource and to allocate new nodes.
 *
 * \note This \ref queue is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref queue_resource_handle on this \ref queue instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p q must not reference a valid \ref queue instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p q is set to a pointer to a valid \ref queue instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On failure, \p q is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
queue_create(
    queue** q, allocator* a)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != q);
    MODEL_ASSERT(prop_allocator_valid(a));

    /* attempt to allocate memory for this queue. */
    queue* tmp = NULL;
    status retval = allocator_allocate(a, (void**)&tmp, sizeof(queue));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(queue));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(queue), queue);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(queue), queue);

    /* set the release method. */
    resource_init(&tmp->hdr, &queue_release);

    /* create the slist instance. */
    retval = slist_create(&(tmp->list), a);
    if (STATUS_SUCCESS != retval)
    {
        /* reclaim the memory for the queue on failure. */
        status reclaim_retval = allocator_reclaim(a, tmp);

        /* bubble up the most pressing error code. */
        if (STATUS_SUCCESS != reclaim_retval)
            return reclaim_retval;
        else
            return retval;
    }

    /* set the queue. */
    *q = tmp;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_queue_valid(*q));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Release a queue resource.
 *
 * \param r             Pointer to the queue resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
static status queue_release(resource* r)
{
    status list_retval, retval;
    queue* q = (queue*)r;

    /* cache the allocator. */
    allocator* a = q->list->alloc;

    /* release the list resource. */
    list_retval = resource_release(slist_resource_handle(q->list));

    /* reclaim this instance. */
    retval = allocator_reclaim(a, q);

    /* if we succeed, then return the status of releasing the list. */
    if (STATUS_SUCCESS == retval)
    {
        return list_retval;
    }
    else
    {
        return retval;
    }
}
