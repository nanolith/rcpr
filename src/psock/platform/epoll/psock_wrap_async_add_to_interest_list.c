/**
 * \file epoll/psock_wrap_async_add_to_interest_list.c
 *
 * \brief Add a psock entry to the underlying subsystem's interest list,
 * whatever that may mean.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_epoll_internal.h"

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
    /* currently a no-op for epoll. */
    (void)sock;
    return STATUS_SUCCESS;
}
