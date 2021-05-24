/**
 * \file kqueue/psock_idle_fiber_entry.c
 *
 * \brief Entry point for the idle fiber for psock I/O.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber/disciplines/psock_io.h>
#include <rcpr/model_assert.h>
#include <sys/types.h>
#include <sys/event.h>

#include "psock_kqueue_internal.h"

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
status psock_idle_fiber_entry(void* context)
{
    status retval;
    bool run_state = true;
    psock_io_kqueue_context* ctx = (psock_io_kqueue_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_kqueue_io_struct_valid(ctx));

    /* loop until termination is requested. */
    while (run_state)
    {
        /* wait on a kqueue event. */
        int nev =
            kevent(
                ctx->kq, ctx->kevent_inputs, ctx->inputs,
                ctx->kevent_outputs, MAX_KEVENT_OUTPUTS, NULL);
        if (nev < 0)
        {
            return ERROR_PSOCK_KEVENT_FAILED;
        }

        /* all inputs have been consumed. */
        ctx->inputs = 0;

        /* loop through all outputs. */
        for (int i = 0; i < nev; ++i)
        {
            fiber* fib = (fiber*)ctx->kevent_outputs[i].udata;
            short filter = ctx->kevent_outputs[i].filter;
            u_short flags = ctx->kevent_outputs[i].flags;
            int resume_event;
            ptrdiff_t resume_param = 0;

            /* encode resume event. */
            if (EVFILT_READ == filter)
            {
                resume_event =
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_READ;
            }
            else
            {
                resume_event =
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_WRITE;
            }

            /* encode resume param value. */
            if (flags & EV_ERROR)
            {
                resume_param |=
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_ERROR;
            }
            if (flags & EV_EOF)
            {
                resume_param |=
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_EOF;
            }

            /* add the fiber back to the run queue; it can now read / write. */
            retval =
                disciplined_fiber_scheduler_add_fiber_to_run_queue(
                    ctx->sched, fib, &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE,
                    resume_event, (void*)resume_param);
            if (STATUS_SUCCESS != retval)
            {
                return retval;
            }
        }

        /* finally, instruct the management discipline to idle this fiber. */
        retval = disciplined_fiber_scheduler_idle_fiber_yield(ctx->sched);
        if (STATUS_SUCCESS != retval)
        {
            run_state = false;
        }
    }

    /* terminate this fiber. */
    return STATUS_SUCCESS;
}
