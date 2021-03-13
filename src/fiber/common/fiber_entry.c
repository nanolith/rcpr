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

/**
 * \brief Entry point for a fiber.
 *
 * \param sched     The fiber scheduler.
 * \param fib       The fiber being entered.
 *
 * \note Does not return.
 */
status fiber_entry(fiber_scheduler* sched, fiber* fib)
{
    /* enter the user function for this fiber. */
    status retval = fib->fn(fib->context);

    /* notify the scheduler that this fiber has completed. */
    int resume_event;
    void* resume_param;
    return
        fiber_scheduler_yield(
            sched, FIBER_SCHEDULER_YIELD_EVENT_STOP, &retval,
            &resume_event, &resume_param);
}
