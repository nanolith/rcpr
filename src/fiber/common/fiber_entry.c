/**
 * \file fiber/common/fiber_entry.c
 *
 * \brief Entry point for a fiber.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_uuid;

/**
 * \brief Entry point for a fiber.
 *
 * \param sched     The fiber scheduler.
 * \param fib       The fiber being entered.
 *
 * \note Does not return.
 */
status RCPR_SYM(fiber_entry)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib)
{
    /* this fiber is now running. */
    fib->fiber_state = FIBER_STATE_RUNNING;

    /* enter the user function for this fiber. */
    status retval = fib->fn(fib->context);

    /* this fiber is now stopped. */
    fib->fiber_state = FIBER_STATE_STOPPED;

    /* notify the scheduler that this fiber has completed. */
    const rcpr_uuid* resume_id = &FIBER_SCHEDULER_INTERNAL_DISCIPLINE;
    int resume_event;
    void* resume_param;
    return
        fiber_scheduler_yield(
            sched, FIBER_SCHEDULER_YIELD_EVENT_STOP, &retval,
            &resume_id, &resume_event, &resume_param);
}
