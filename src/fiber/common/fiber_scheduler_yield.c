/**
 * \file fiber/common/fiber_scheduler_yield.c
 *
 * \brief Yield to the fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Yield to the fiber scheduler.
 *
 * \param sched         The scheduler.
 * \param yield_event   The yield event.
 * \param yield_param   The yield event parameter.
 * \param resume_event  Pointer to receive the resume event.
 * \param resume_param  Pointer to receive the resume parameter.
 *
 * \note The currently executing fiber can call yield to yield to the scheduler.
 * The yield event describes the event causing the yield; the yield parameter
 * can be used to send an optional parameter to the scheduler.  When the fiber
 * is resumed, the resume event describes why it was resumed, and the resume
 * parameter holds an optional parameter for the resume.  This can be used to
 * implement coroutines or to implement a blocking I/O simulation by yielding
 * when an I/O operation on a non-blocking socket would block.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, the scheduler will suspend this fiber and start another.
 *        As far as the fiber is concerned, it will restart when the scheduler
 *        determines that it should restart.
 */
status FN_DECL_MUST_CHECK
fiber_scheduler_yield(
    fiber_scheduler* sched, int yield_event, void* yield_param,
    int* resume_event, void** resume_param)
{
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(NULL != resume_event);
    MODEL_ASSERT(NULL != resume_param);

    /* call the callback function to yield to the scheduler. */
    fiber* resume_fib;
    int resume_event1;
    void* resume_param1;
    retval =
        sched->fn(
            sched->context, sched->current_fiber, yield_event, yield_param,
            &resume_fib, &resume_event1, &resume_param1);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* set the current fiber to the resume fiber. */
    /* TODO - do a context switch here. */
    sched->current_fiber = resume_fib;
    *resume_event = resume_event1;
    *resume_param = resume_param1;

    /* success. */
    goto done;

done:
    return retval;
}
