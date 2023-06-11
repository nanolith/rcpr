/**
 * \file epoll/psock_fiber_scheduler_disciplined_write_wait_callback_handler.c
 *
 * \brief Handle a write wait callback via epoll.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <string.h>

#include "psock_epoll_internal.h"

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
    status retval;
    struct epoll_event event;

    /* unused parameters. */
    (void)yield_fib;
    (void)yield_event;

    psock_io_epoll_context* ctx = (psock_io_epoll_context*)context;
    psock_wrap_async* ps = (psock_wrap_async*)yield_param;
    psock_from_descriptor* desc = (psock_from_descriptor*)ps->wrapped;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));
    RCPR_MODEL_ASSERT(prop_fiber_valid(yield_fib));
    RCPR_MODEL_ASSERT(desc->descriptor >= 0);

    /* set the epoll control for this yield event. */
    memset(&event, 0, sizeof(event));
    event.events = EPOLLONESHOT;

    /* if we are blocked for reading, set the read event. */
    if (NULL != ps->read_block_fib)
    {
        event.events |= EPOLLIN;
    }

    /* if we are blocked for write, set the write event. */
    if (NULL != ps->write_block_fib)
    {
        event.events |= EPOLLOUT;
    }

    /* the data pointer should be for the psock_wrap_async instance. */
    event.data.ptr = ps;

    /* attempt to modify an existing epoll instance for this fd. */
    retval = epoll_ctl(ctx->ep, EPOLL_CTL_MOD, desc->descriptor, &event);
    if (retval < 0 && errno == ENOENT)
    {
        /* fall back to adding an entry for this fd. */
        retval = epoll_ctl(ctx->ep, EPOLL_CTL_ADD, desc->descriptor, &event);
    }

    /* verify the result of mod / add. */
    if (retval < 0)
    {
        return ERROR_PSOCK_EPOLL_CTL_FAILED;
    }

    /* success. */
    return STATUS_SUCCESS;
}
