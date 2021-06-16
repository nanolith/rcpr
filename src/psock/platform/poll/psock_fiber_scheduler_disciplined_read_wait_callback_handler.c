/**
 * \file select/psock_fiber_scheduler_disciplined_read_wait_callback_handler.c
 *
 * \brief Handle a read wait callback via select.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>

#include "psock_poll_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;

/**
 * \brief Callback for read wait events.
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
status psock_fiber_scheduler_disciplined_read_wait_callback_handler(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
     void* yield_param)
{
    status retval;

    /* unused parameter. */
    (void)yield_event;

    psock_io_poll_context* ctx = (psock_io_poll_context*)context;
    int fd = (int)((ptrdiff_t)yield_param);

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_poll_io_struct_valid(ctx));
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(fb >= 0);

    /* do we need to allocate more memory for the poll events structure? */
    if (ctx->poll_curr == ctx->poll_max)
    {
        /* increase the event array size. */
        size_t newsize = ctx->poll_max + POLL_EVENT_SIZE_INCREMENT;
        retval =
            allocator_reallocate(
                ctx->alloc, (void**)&ctx->poll_events,
                newsize * sizeof(struct pollfd));
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }

        /* increase the fiber array size. */
        retval =
            allocator_reallocate(
                ctx->alloc, (void**)&ctx->poll_fibers,
                newsize * sizeof(fiber*));
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }

        /* set the new max size. */
        ctx->poll_max = newsize;
    }

    /* add this event to the poll structure. */
    size_t idx = ctx->poll_curr;
    ctx->poll_events[idx].fd = fd;
    ctx->poll_events[idx].events = POLLIN;
    ctx->poll_events[idx].revents = 0;
    ctx->poll_fibers[idx] = yield_fib;

    /* increment the number of active events. */
    ++(ctx->poll_curr);

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}
