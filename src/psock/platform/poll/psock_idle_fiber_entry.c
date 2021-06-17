/**
 * \file select/psock_idle_fiber_entry.c
 *
 * \brief Entry point for the idle fiber for psock I/O.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber/disciplines/psock_io.h>
#include <rcpr/model_assert.h>
#include <string.h>

#include "psock_poll_internal.h"

RCPR_IMPORT_fiber;

/**
 * \brief The entry point for the psock idle fiber.
 *
 * This idle fiber handles the platform-specific event loop for I/O events, and
 * will sleep until a descriptor is available for a requested read or write.
 *
 * \param context       The user context for this fiber.
 *
 * \returns a status code indicating success or failure when this fiber
 * terminates.
 */
status RCPR_SYM(psock_idle_fiber_entry)(void* context)
{
    status retval, set_retval;
    bool run_state = true;
    psock_io_poll_context* ctx = (psock_io_poll_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_poll_io_struct_valid(ctx));

    /* loop until termination is requested. */
    while (run_state)
    {
        /* wait on a poll event. */
        int nev = poll(ctx->poll_events, ctx->poll_curr, -1);
        if (nev < 0)
        {
            retval = ERROR_PSOCK_POLL_FAILED;
            goto done;
        }

        /* loop through all outputs. */
        size_t new_curr = 0;
        for (size_t i = 0; i < ctx->poll_curr; ++i)
        {
            fiber* fib = ctx->poll_fibers[i];
            short events = ctx->poll_events[i].events;
            short revents = ctx->poll_events[i].revents;
            int resume_event = -1;
            ptrdiff_t resume_param = 0;

            /* encode a resume event. */
            if (revents & POLLIN)
            {
                resume_event =
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_READ;
            }
            else if (revents & POLLOUT)
            {
                resume_event =
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_WRITE;
            }
            else if (revents & POLLHUP)
            {
                if (events & POLLIN)
                {
                    resume_event =
                        FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_READ;
                }
                else
                {
                    resume_event =
                        FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_WRITE;
                }
            }

            /* encode resume param value. */
            if (revents & POLLERR)
            {
                resume_param |=
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_ERROR;
            }
            if (revents & POLLHUP)
            {
                resume_param |=
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_EOF;
            }

            /* was an event recorded? */
            if (-1 != resume_event)
            {
                /* add the fiber back to the run queue. */
                retval =
                    disciplined_fiber_scheduler_add_fiber_to_run_queue(
                        ctx->sched, fib, &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE,
                        resume_event, (void*)resume_param);
                if (STATUS_SUCCESS != retval)
                {
                    goto done;
                }
            }
            else
            {
                /* otherwise, move this event to the next available slot. */
                if (i != new_curr)
                {
                    ctx->poll_fibers[new_curr] = ctx->poll_fibers[i];
                    memcpy(
                        &ctx->poll_events[new_curr], &ctx->poll_events[i],
                        sizeof(struct pollfd));
                }

                ++new_curr;
            }
        }

        /* update the number of currently active events. */
        ctx->poll_curr = new_curr;

        /* finally, instruct the management discipline to idle this fiber. */
        retval = disciplined_fiber_scheduler_idle_fiber_yield(ctx->sched);
        if (STATUS_SUCCESS != retval)
        {
            run_state = false;
        }
    }

    /* terminate this fiber. */
    retval = STATUS_SUCCESS;

done:
    set_retval = disciplined_fiber_scheduler_set_idle_fiber(ctx->sched, NULL);
    if (STATUS_SUCCESS != set_retval)
    {
        retval = set_retval;
    }

    return retval;
}
