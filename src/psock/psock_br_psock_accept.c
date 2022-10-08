/**
 * \file psock/psock_br_psock_accept.c
 *
 * \brief Accept a socket from a listen descriptor.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Accept a socket from a \ref psock listen socket instance.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param desc          Pointer to the integer field to hold the accepted
 *                      descriptor.
 * \param addr          The address of the accepted socket.
 * \param addrlen       On input, the max size of the address field; on output,
 *                      the size of the address field.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_br_psock_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    psock_br* br = (psock_br*)sock;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(br));

    /* pass through to the wrapped socket. */
    return br->wrapped->accept_fn(br->wrapped, desc, addr, addrlen);
}
