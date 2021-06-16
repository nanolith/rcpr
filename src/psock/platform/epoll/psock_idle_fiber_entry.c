/**
 * \file epoll/psock_idle_fiber_entry.c
 *
 * \brief Entry point for the idle fiber for psock I/O.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>
#include <rcpr/fiber/disciplines/psock_io.h>
#include <rcpr/model_assert.h>
#include <sys/types.h>

#include "psock_epoll_internal.h"

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
status psock_idle_fiber_entry(void* context)
{
    status retval, set_retval;
    bool run_state = true;
    psock_io_epoll_context* ctx = (psock_io_epoll_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));

    /* loop until termination is requested. */
    while (run_state)
    {
        /* wait on an epoll event. */
        int nev =
            epoll_wait(
                ctx->ep, ctx->epoll_outputs, MAX_EPOLL_OUTPUTS, -1);
        if (nev < 0)
        {
            retval = ERROR_PSOCK_EPOLL_WAIT_FAILED;
            goto done;
        }

        /* loop through all outputs. */
        for (int i = 0; i < nev; ++i)
        {
            fiber* fib = (fiber*)ctx->epoll_outputs[i].data.ptr;
            uint32_t filter = ctx->epoll_outputs[i].events;
            int resume_event;
            ptrdiff_t resume_param = 0;

            /* encode resume event. */
            if (filter & EPOLLIN)
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
            if (filter & EPOLLERR)
            {
                resume_param |=
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_ERROR;
            }
            if (filter & EPOLLHUP)
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
                goto done;
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
    retval = STATUS_SUCCESS;

done:
    set_retval = disciplined_fiber_scheduler_set_idle_fiber(ctx->sched, NULL);
    if (STATUS_SUCCESS != set_retval)
    {
        retval = set_retval;
    }

    return retval;
}
