/**
 * \file platform/pthread/thread/thread_mutex_create.c
 *
 * \brief Create a mutex.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "thread_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

/* forward decls. */
static status thread_mutex_release(resource*);
static status thread_mutex_lock_release(resource*);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_mutex);
MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_mutex_lock);

/**
 * \brief Create a \ref thread_mutex instance.
 *
 * \param mut           Pointer to the \ref thread_mutex pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      thread_mutex resource.
 *
 * \note This \ref thread_mutex is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * thread_mutex_resource_handle on this \ref thread_mutex instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p mut must not reference a valid \ref thread_mutex instance and must
 *        not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p mut is set to a pointer to a valid \ref thread_mutex
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p lock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(thread_mutex_create)(
    RCPR_SYM(thread_mutex)** mut, RCPR_SYM(allocator)* a)
{
    int retval, reclaim_retval;
    thread_mutex* tmp;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != mut);
    MODEL_ASSERT(prop_allocator_valid(a));

    /* attempt to allocate memory for this mutex. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(thread_mutex));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(thread_mutex));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(thread_mutex), thread_mutex);

    /* the child tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->child.MODEL_STRUCT_TAG_REF(thread_mutex_lock), thread_mutex_lock);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(
        tmp->MODEL_STRUCT_TAG_REF(thread_mutex), thread_mutex);

    /* set the release method. */
    resource_init(&tmp->hdr, &thread_mutex_release);

    /* save the init values. */
    tmp->alloc = a;

    /* initialize the pthread_mutex. */
    retval = pthread_mutex_init(&tmp->mutex, NULL);
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_THREAD_MUTEX_INIT;
        goto free_thread_mutex;
    }

    /* set the release method for the mutex lock. */
    resource_init(&tmp->child.hdr, &thread_mutex_lock_release);

    /* set the parent for the lock. */
    tmp->child.parent = tmp;

    /* set the child tag. */
    MODEL_STRUCT_TAG_INIT(
        tmp->child.MODEL_STRUCT_TAG_REF(thread_mutex_lock), thread_mutex_lock);

    /* set the return pointer. */
    *mut = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_thread_mutex_valid(*mut));

    /* verify that the child structure is now valid. */
    MODEL_ASSERT(prop_thread_mutex_lock_valid(&(*mut)->child));

    /* success. skip to done. */
    goto done;

free_thread_mutex:
    memset(tmp, 0, sizeof(thread_mutex));
    reclaim_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS != reclaim_retval)
        retval = reclaim_retval;

done:
    return retval;
}

/**
 * \brief Release a \ref thread_mutex instance.
 *
 * \param r         The \ref thread_mutex \ref resource to release.
 *
 * \returns a status code indicating success or failure.
 */
static status thread_mutex_release(resource* r)
{
    status retval, mutex_retval;
    thread_mutex* mut = (thread_mutex*)r;
    MODEL_ASSERT(prop_thread_mutex_valid(mut));

    /* cache the allocator. */
    allocator* a = mut->alloc;

    /* destroy the pthread_mutex. */
    retval = pthread_mutex_destroy(&mut->mutex);
    if (STATUS_SUCCESS != retval)
    {
        mutex_retval = ERROR_THREAD_MUTEX_DESTROY;
    }
    else
    {
        mutex_retval = STATUS_SUCCESS;
    }

    /* clear the mutex structure. */
    memset(mut, 0, sizeof(thread_mutex));

    /* reclaim the mutex structure. */
    retval = allocator_reclaim(a, mut);

    /* if we succeeded at reclaiming the mutex structure, return the */
    /* mutex retval. */
    if (STATUS_SUCCESS == retval)
    {
        return mutex_retval;
    }
    else
    {
        return retval;
    }
}

/**
 * \brief Release a \ref thread_mutex_lock instance.
 *
 * \param r         The \ref thread_mutex_lock \ref resource to release.
 *
 * \returns a status code indicating success or failure.
 */
static status thread_mutex_lock_release(resource* r)
{
    status retval;
    thread_mutex_lock* lock = (thread_mutex_lock*)r;
    MODEL_ASSERT(prop_thread_mutex_lock_valid(lock));

    /* unlock the pthread_mutex. */
    retval = pthread_mutex_unlock(&lock->parent->mutex);
    if (STATUS_SUCCESS != retval)
    {
        return ERROR_THREAD_MUTEX_UNLOCK;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}
