/**
 * \file fiber/common/fiber_scheduler_create.c
 *
 * \brief Create a fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/* forward decls. */
MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber_scheduler);

/**
 * \brief Create a \ref fiber_scheduler instance.
 *
 * \param sched         Pointer to the \ref fiber_scheduler pointer to receive
 *                      this resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber_scheduler resource.
 * \param context       An opaque pointer to a context structure to use for this
 *                      \ref fiber_scheduler instance.
 * \param fn            The scheduling function for this \ref fiber_scheduler.
 *
 * \note This \ref fiber_scheduler is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * fiber_scheduler_resource_handle on this \ref fiber_scheduler instance. The
 * fiber_scheduler must be in a terminated state before releasing this resource.
 * If the fiber_scheduler is not yet terminated, then undefined behavior can
 * occur.  It is up to the caller to ensure that the fiber_scheduler has
 * terminated, such as devising a termination strategy, prior to releasing this
 * resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sched must not reference a valid \ref fiber_scheduler instance and
 *        must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p fn must be a valid function.
 *
 * \post
 *      - On success, \p sched is set to a pointer to a valid
 *        \ref fiber_scheduler instance, which is a \ref resource owned by the
 *        caller that must be released by the caller when no longer needed.
 *      - On failure, \p sched is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
fiber_scheduler_create(
    fiber_scheduler** sched, allocator* a, void* context,
    fiber_scheduler_callback_fn fn)
{
    fiber_scheduler* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != sched);
    MODEL_ASSERT(NULL != fn);

    /* attempt to allocate memory for this fiber_scheduler. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(fiber_scheduler));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(fiber_scheduler));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(fiber_scheduler), fiber_scheduler);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(
        tmp->MODEL_STRUCT_TAG_REF(fiber_scheduler), fiber_scheduler);

    /* set the release method. */
    resource_init(&tmp->hdr, &fiber_scheduler_resource_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->main_fiber = NULL;
    tmp->context = context;
    tmp->fn = fn;

    /* create the main fiber. */
    retval = fiber_create_for_thread(&tmp->main_fiber, tmp->alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fiber_scheduler;
    }

    /* call the callback function to add this main fiber. */
    fiber* resume_fib;
    int resume_event;
    void* resume_param;
    retval =
        tmp->fn(
            tmp->context, tmp->main_fiber, FIBER_SCHEDULER_YIELD_EVENT_MAIN,
            NULL, &resume_fib, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fiber_scheduler;
    }

    /* verify that our resume point was correct after adding main. */
    if (       resume_fib != tmp->main_fiber
            || resume_event != FIBER_SCHEDULER_RESUME_EVENT_MAIN)
    {
        retval = ERROR_FIBER_SCHEDULER_CALLBACK_STATE;
        goto cleanup_fiber_scheduler;
    }

    /* set the current fiber to the main fiber. */
    tmp->current_fiber = tmp->main_fiber;

    /* set the return pointer. */
    *sched = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(*sched));

    /* success. */
    goto done;

cleanup_fiber_scheduler:
    release_retval = resource_release(fiber_scheduler_resource_handle(tmp));
    if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }

done:
    return retval;
}
