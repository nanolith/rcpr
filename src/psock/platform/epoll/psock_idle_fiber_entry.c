/**
 * \file epoll/psock_idle_fiber_entry.c
 *
 * \brief Entry point for the idle fiber for psock I/O.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/fiber.h>
#include <rcpr/fiber/disciplines/psock_io.h>
#include <rcpr/model_assert.h>
#include <string.h>
#include <sys/types.h>

#include "psock_epoll_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_psock_internal;

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
    psock_io_epoll_context* ctx = (psock_io_epoll_context*)context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));

    /* loop until termination is requested. */
    while (run_state)
    {
        /* wait on an epoll event. */
        int nev =
            epoll_wait(
                ctx->ep, ctx->epoll_outputs, MAX_EPOLL_OUTPUTS, -1);
        if (nev < 0 && errno == EINTR)
        {
            /* if we are interrupted (e.g. from debugging) try again. */
            continue;
        }
        else if (nev < 0)
        {
            retval = ERROR_PSOCK_EPOLL_WAIT_FAILED;
            goto done;
        }

        /* loop through all outputs. */
        for (int i = 0; i < nev; ++i)
        {
            psock_wrap_async* ps =
                (psock_wrap_async*)ctx->epoll_outputs[i].data.ptr;
            psock_from_descriptor* desc = (psock_from_descriptor*)ps->wrapped;
            uint32_t filter = ctx->epoll_outputs[i].events;
            struct epoll_event event;

            /* clear the event. */
            memset(&event, 0, sizeof(event));
            event.events = EPOLLONESHOT;

            /* check for a read resume event. */
            if ((filter & EPOLLIN) && NULL != ps->read_block_fib)
            {
                ptrdiff_t resume_param = 0;
                int resume_event =
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_READ;

                /* check for an error. */
                if (filter & EPOLLERR)
                {
                    resume_param |=
                        FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_ERROR;
                }

                /* check for a hang-up. Be sure to check for read hang-up. */
                if (filter & EPOLLHUP || filter & EPOLLRDHUP)
                {
                    resume_param |=
                        FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_EOF;
                }

                /* add the fiber back to the run queue; it can now read. */
                retval =
                    disciplined_fiber_scheduler_add_fiber_to_run_queue(
                        ctx->sched, ps->read_block_fib,
                        &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE, resume_event,
                        (void*)resume_param);
                if (STATUS_SUCCESS != retval)
                {
                    goto done;
                }

                /* remove this fiber from the list of blockers. */
                ps->read_block_fib = NULL;
            }

            /* check for a write resume event. */
            if ((filter & EPOLLOUT) && NULL != ps->write_block_fib)
            {
                ptrdiff_t resume_param = 0;
                int resume_event =
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_WRITE;

                /* check for an error. */
                if (filter & EPOLLERR)
                {
                    resume_param |=
                        FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_ERROR;
                }

                /* check for a hang-up. */
                if (filter & EPOLLHUP)
                {
                    resume_param |=
                        FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_FLAG_EOF;
                }

                /* add the fiber back to the run queue; it can now write. */
                retval =
                    disciplined_fiber_scheduler_add_fiber_to_run_queue(
                        ctx->sched, ps->write_block_fib,
                        &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE, resume_event,
                        (void*)resume_param);
                if (STATUS_SUCCESS != retval)
                {
                    goto done;
                }

                /* remove this fiber from the list of blockers. */
                ps->write_block_fib = NULL;
            }

            /* should we re-arm the epoll trigger? */
            if (NULL != ps->read_block_fib || NULL != ps->write_block_fib)
            {
                /* arm the input filter? */
                if (NULL != ps->read_block_fib)
                {
                    event.events |= EPOLLIN;
                }

                /* arm the output filter? */
                if (NULL != ps->write_block_fib)
                {
                    event.events |= EPOLLOUT;
                }

                /* set the data pointer. */
                event.data.ptr = ps;

                /* attempt to modify an existing epoll instance for this fd. */
                retval =
                    epoll_ctl(ctx->ep, EPOLL_CTL_MOD, desc->descriptor, &event);
                if (retval < 0 && errno == ENOENT)
                {
                    /* fall back to adding an entry for this fd. */
                    retval =
                        epoll_ctl(
                            ctx->ep, EPOLL_CTL_ADD, desc->descriptor, &event);

                    /* TODO - we can't really do anything yet if this fails. */
                    (void)retval;
                }
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
