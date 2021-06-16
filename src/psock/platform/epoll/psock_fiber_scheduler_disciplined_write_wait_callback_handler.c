/**
 * \file epoll/psock_fiber_scheduler_disciplined_write_wait_callback_handler.c
 *
 * \brief Handle a write wait callback via epoll.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>

#include "psock_epoll_internal.h"

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
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval;
    struct epoll_event event;

    /* unused parameter. */
    (void)yield_event;

    psock_io_epoll_context* ctx = (psock_io_epoll_context*)context;
    int fd = (int)((ptrdiff_t)yield_param);

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(fd >= 0);

    /* set the epoll control for this yield event. */
    event.events = EPOLLOUT | EPOLLONESHOT;
    event.data.ptr = yield_fib;
    retval = epoll_ctl(ctx->ep, EPOLL_CTL_MOD, fd, &event);
    if (retval < 0 && errno == ENOENT)
    {
        retval = epoll_ctl(ctx->ep, EPOLL_CTL_ADD, fd, &event);
    }
    if (retval < 0)
    {
        return ERROR_PSOCK_EPOLL_CTL_FAILED;
    }

    /* success. */
    return STATUS_SUCCESS;
}
