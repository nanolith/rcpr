/**
 * \file platform/pthread/thread/thread_create.c
 *
 * \brief Create and begin executing a new thread.
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
static status thread_release(resource*);
static void* thread_start(void*);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread);

/**
 * \brief Create a \ref thread instance.
 *
 * \param th            Pointer to the \ref thread pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      thread resource.
 * \param stack_size    The size of the stack in bytes for this thread.
 * \param context       An opaque pointer to a context structure to use for this
 *                      thread instance.
 * \param fn            The function this thread should execute.
 *
 * \note This \ref thread is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref thread_resource_handle on this \ref thread instance. If the thread is
 * still executing, the resource release will block until the thread stops. It
 * is up to the caller to devise a mechanism to stop the thread.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p th must not reference a valid \ref thread instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p stack_size must be greater than zero and must follow platform rules
 *        for thread stack size.
 *      - \p fn must be a valid function.
 *
 * \post
 *      - On success, \p th is set to a pointer to a valid \ref thread instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On success, a thread of execution will begin executing \p fn.
 *      - On failure, \p q is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(thread_create)(
    RCPR_SYM(thread)** th, RCPR_SYM(allocator)* a, size_t stack_size,
    void* context, RCPR_SYM(thread_fn) fn)
{
    status retval, reclaim_retval;
    pthread_attr_t attr;
    thread* tmp = NULL;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != th);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(stack_size > 0);
    RCPR_MODEL_ASSERT(NULL != fn);

    /* create a thread attribute structure. */
    retval = pthread_attr_init(&attr);
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_THREAD_ATTRIBUTE_INIT;
        goto done;
    }

    /* set the stack size. */
    retval = pthread_attr_setstacksize(&attr, stack_size);
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_THREAD_ATTRIBUTE_SETSTACKSIZE;
        goto cleanup_attr;
    }

    /* attempt to allocate memory for this thread. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(thread));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto cleanup_attr;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(thread));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(thread), thread);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(tmp->RCPR_MODEL_STRUCT_TAG_REF(thread), thread);

    /* set the release method. */
    resource_init(&tmp->hdr, &thread_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->context = context;
    tmp->fn = fn;
    tmp->running = true;

    /* create the pthread. */
    retval = pthread_create(&tmp->thread, &attr, &thread_start, tmp);
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_THREAD_CREATE;
        goto free_thread;
    }

    /* Set the return pointer. */
    *th = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_thread_valid(*th));

    /* success.  Clean up the thread attribute structure. */
    goto cleanup_attr;

free_thread:
    memset(tmp, 0, sizeof(thread));
    reclaim_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS != reclaim_retval)
        retval = reclaim_retval;

cleanup_attr:
    pthread_attr_destroy(&attr);

done:
    return retval;
}

/**
 * \brief Start a thread instance, bootstrapped from a pthread.
 *
 * \param ctx       The thread context for this thread.
 */
static void* thread_start(void* ctx)
{
    /* get the thread instance and verify it is valid. */
    thread* th = (thread*)ctx;
    RCPR_MODEL_ASSERT(prop_thread_valid(th));

    /* run the thread function. */
    th->exit_code = th->fn(th->context);

    /* the thread function is done, so set running to false. */
    th->running = false;

    /* we'll never hit this point, but follow the spec. */
    return NULL;
}

/**
 * \brief Release a thread instance, joining it.
 *
 * \param r         The thread resource to release.
 *
 * \returns a status code indicating success or failure, which is the thread's
 *          exiting status code if it is successfully joined.
 */
static status thread_release(resource* r)
{
    status thread_retval, retval;
    thread* th = (thread*)r;
    RCPR_MODEL_ASSERT(prop_thread_valid(th));

    /* cache the allocator. */
    allocator* a = th->alloc;

    /* join the thread. */
    retval = pthread_join(th->thread, NULL);
    if (STATUS_SUCCESS != retval)
    {
        thread_retval = ERROR_THREAD_JOIN;
    }
    else
    {
        thread_retval = th->exit_code;
    }

    /* clear the thread structure. */
    memset(th, 0, sizeof(thread));

    /* reclaim the thread structure. */
    retval = allocator_reclaim(a, th);

    /* if we succeded at reclaiming the thread structure, return the */
    /* thread_retval. */
    if (STATUS_SUCCESS == retval)
    {
        return thread_retval;
    }
    else
    {
        return retval;
    }
}
