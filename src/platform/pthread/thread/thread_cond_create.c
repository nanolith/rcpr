/**
 * \file platform/pthread/thread/thread_cond_create.c
 *
 * \brief Create a thread condition variable.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "thread_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

/* forward decls. */
static status thread_cond_release(resource*);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_cond);

/* the vtable entry for the thread cond instance. */
RCPR_VTABLE
resource_vtable thread_cond_vtable = {
    &thread_cond_release };

/**
 * \brief Create a \ref thread_cond instance.
 *
 * \param cond          Pointer to the \ref thread_cond pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      thread_mutex resource.
 *
 * \note This \ref thread_cond is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * thread_cond_resource_handle on this \ref thread_cond instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p cond must not reference a valid \ref thread_cond instance and must
 *        not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p cond is set to a pointer to a valid \ref thread_cond
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p cond is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(thread_cond_create)(
    RCPR_SYM(thread_cond)** cond, RCPR_SYM(allocator)* a)
{
    int retval, reclaim_retval;
    thread_cond* tmp;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != cond);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));

    /* attempt to allocate memory for this condition variable. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(thread_cond));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(thread_cond));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(thread_cond), thread_cond);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(thread_cond), thread_cond);

    /* set the release method. */
    resource_init(&tmp->hdr, &thread_cond_vtable);

    /* save the init values. */
    tmp->alloc = a;

    /* initialize the pthread_cond. */
    retval = pthread_cond_init(&tmp->cond, NULL);
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_THREAD_COND_INIT;
        goto free_thread_cond;
    }

    /* set the return pointer. */
    *cond = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_thread_cond_valid(*cond));

    /* success. skip to done. */
    goto done;

free_thread_cond:
    memset(tmp, 0, sizeof(thread_cond));
    reclaim_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS != reclaim_retval)
        retval = reclaim_retval;

done:
    return retval;
}

/**
 * \brief Release a \ref thread_cond instance.
 *
 * \param r         The \ref thread_cond \ref resource to release.
 *
 * \returns a status code indicating success or failure.
 */
static status thread_cond_release(resource* r)
{
    status retval, cond_retval;
    thread_cond* cond = (thread_cond*)r;
    RCPR_MODEL_ASSERT(prop_thread_cond_valid(cond));

    /* cache the allocator. */
    allocator* a = cond->alloc;

    /* destroy the pthread_cond. */
    retval = pthread_cond_destroy(&cond->cond);
    if (STATUS_SUCCESS != retval)
    {
        cond_retval = ERROR_THREAD_COND_DESTROY;
    }
    else
    {
        cond_retval = STATUS_SUCCESS;
    }

    /* clear the cond structure. */
    memset(cond, 0, sizeof(thread_cond));

    /* reclaim the cond structure. */
    retval = allocator_reclaim(a, cond);

    /* if we succeeded at reclaiming the cond structure, return the */
    /* cond retval. */
    if (STATUS_SUCCESS == retval)
    {
        return cond_retval;
    }
    else
    {
        return retval;
    }
}
