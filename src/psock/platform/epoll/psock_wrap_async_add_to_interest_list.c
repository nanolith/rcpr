/**
 * \file epoll/psock_wrap_async_add_to_interest_list.c
 *
 * \brief Add a psock entry to the underlying subsystem's interest list,
 * whatever that may mean.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>

#include "psock_epoll_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_psock_internal;

/**
 * \brief Instruct the underlying async fiber discipline to add this socket to
 * the interest list.
 *
 * \param sock          Pointer to the socket instance to add to the interest
 *                      list.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_wrap_async_add_to_interest_list)(
    RCPR_SYM(psock_wrap_async)* sock)
{
    status retval;
    struct epoll_event event;
    psock_io_epoll_context* ctx =
        (psock_io_epoll_context*)fiber_scheduler_discipline_context_get(
            sock->psock_discipline);
    psock_from_descriptor* pchild = (psock_from_descriptor*)sock->wrapped;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_wrap_async_valid(sock));
    RCPR_MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));
    RCPR_MODEL_ASSERT(PSOCK_TYPE_DESCRIPTOR == sock->wrapped->type);

    /* add this event to the interest list. */
    event.events = 0;
    event.data.ptr = NULL;
    retval = epoll_ctl(ctx->ep, EPOLL_CTL_ADD, pchild->descriptor, &event);
    if (retval < 0)
    {
        return ERROR_PSOCK_EPOLL_CTL_FAILED;
    }

    /* success. */
    return STATUS_SUCCESS;
}
