/**
 * \file fiber/common/fiber_scheduler_add.c
 *
 * \brief Add a fiber to the scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;

/**
 * \brief Add a fiber to the \ref fiber_scheduler.
 *
 * \param sched         The scheduler to which this \ref fiber is added.
 * \param fib           The \ref fiber to add.
 *
 * \note The \ref fiber_scheduler takes ownership of this \ref fiber and will
 * release it by calling \ref resource_release on its \ref fiber_resource_handle
 * when no longer needed.  Ultimately, it is up to the callback method for this
 * \ref fiber_scheduler to maintain ownership of this \ref fiber until it is no
 * longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance.
 *      - The caller owns \p fib.
 *
 * \post
 *      - On success, \p sched takes ownership of \p fib.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_add)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib)
{
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_fiber_valid(fib));

    /* call the callback function to add this fiber. */
    fiber* resume_fib;
    const rcpr_uuid* resume_id = &FIBER_SCHEDULER_INTERNAL_DISCIPLINE;
    int resume_event;
    void* resume_param;
    retval =
        sched->fn(
            sched->context, sched->current_fiber,
            FIBER_SCHEDULER_YIELD_EVENT_ADD_FIBER, fib,
            &resume_fib, &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* set the current fiber to the resume fiber. */
    fiber* prev = sched->current_fiber;
    fiber* next = resume_fib;
    sched->current_fiber = resume_fib;

    /* switch the fibers. */
    fiber_switch(prev, next, resume_id, resume_event, resume_param);

    /* success. */
    goto done;

done:
    return retval;
}
