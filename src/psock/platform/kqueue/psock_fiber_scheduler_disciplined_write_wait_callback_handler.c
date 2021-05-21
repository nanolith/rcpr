/**
 * \file kqueue/psock_fiber_scheduler_disciplined_write_wait_callback_handler.c
 *
 * \brief Handle a write wait callback via kqueue.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../psock_internal.h"

/**
 * \brief Callback for write wait events.
 *
 * \param context       The user context for this callback.
 * \param yield_fib     The yielding fiber for this event.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   The yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
status psock_fiber_scheduler_disciplined_write_wait_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    /* TODO - fill out stub. */
    (void)context;
    (void)yield_fib;
    (void)yield_event;
    (void)yield_param;

    return -1;
}
