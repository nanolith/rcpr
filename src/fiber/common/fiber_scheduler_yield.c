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
 * \param sched             The scheduler.
 * \param yield_event       The yield event.
 * \param yield_param       The yield event parameter.
 * \param resume_disc_id    Pointer to receive the pointer to the discipline id
 *                          for this restore event. Note: the stored pointer
 *                          should be GUARANTEED to outlive the life of the
 *                          fiber.
 * \param resume_event      Pointer to receive the resume event.
 * \param resume_param      Pointer to receive the resume parameter.
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
    const rcpr_uuid** resume_disc_id, int* resume_event, void** resume_param)
{
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(NULL != resume_disc_id);
    MODEL_ASSERT(NULL != resume_event);
    MODEL_ASSERT(NULL != resume_param);

    /* call the callback function to yield to the scheduler. */
    fiber* resume_fib;
    const rcpr_uuid* resume_id = &FIBER_SCHEDULER_INTERNAL_DISCIPLINE;
    int resume_event1;
    void* resume_param1;
    retval =
        sched->fn(
            sched->context, sched->current_fiber, yield_event, yield_param,
            &resume_fib, &resume_id, &resume_event1, &resume_param1);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* set the current fiber to the resume fiber. */
    fiber* prev = sched->current_fiber;
    fiber* next = resume_fib;
    sched->current_fiber = resume_fib;

    /* switch the fibers. */
    fiber_switch(prev, next, resume_id, resume_event1, resume_param1);

    /* here's where things get hairy. The fiber_switch returns when this old
     * fiber has been re-activated.
     */
    *resume_disc_id = sched->current_fiber->restore_discipline_id;
    *resume_event = sched->current_fiber->restore_reason_code;
    *resume_param = sched->current_fiber->restore_param;

    /* success. */
    goto done;

done:
    return retval;
}
