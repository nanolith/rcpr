/**
 * \file kqueue/psock_fiber_scheduler_disciplined_write_wait_callback_handler.c
 *
 * \brief Handle a write wait callback via kqueue.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <sys/types.h>
#include <sys/event.h>

#include "psock_kqueue_internal.h"

RCPR_IMPORT_psock_internal;

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
status RCPR_SYM(psock_fiber_scheduler_disciplined_write_wait_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    /* unused parameter. */
    (void)yield_event;

    psock_io_kqueue_context* ctx = (psock_io_kqueue_context*)context;
    psock_wrap_async* ps = (psock_wrap_async*)yield_param;
    psock_from_descriptor* desc = (psock_from_descriptor*)ps->wrapped;
    int fd = desc->descriptor;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_kqueue_io_struct_valid(ctx));
    RCPR_MODEL_ASSERT(prop_fiber_valid(yield_fib));
    RCPR_MODEL_ASSERT(fd >= 0);

    /* event structure invariant. */
    RCPR_MODEL_ASSERT(ctx->inputs < MAX_KEVENT_INPUTS);

    /* set the kevent for this yield event. */
    EV_SET(
        &ctx->kevent_inputs[ctx->inputs], fd,
        EVFILT_WRITE,
        EV_ONESHOT | EV_ADD | EV_ENABLE, 0, 0, yield_fib);

    /* increment inputs. */
    ++(ctx->inputs);

    /* invariant check: have we reached max input size? */
    if (ctx->inputs == MAX_KEVENT_INPUTS)
    {
        ctx->inputs = 0;

        /* add the inputs to kevent. */
        int nev =
            kevent(
                ctx->kq, ctx->kevent_inputs, MAX_KEVENT_INPUTS,
                ctx->kevent_outputs, 0, NULL);
        if (0 != nev)
        {
            return ERROR_PSOCK_KEVENT_FAILED;
        }
    }

    /* success. */
    return STATUS_SUCCESS;
}
