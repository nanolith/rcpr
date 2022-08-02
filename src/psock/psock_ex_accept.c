/**
 * \file psock/psock_ex_accept.c
 *
 * \brief Accept a socket from a user psock instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/psock.h>
#include <string.h>

#include "psock_internal.h"

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
status RCPR_SYM(psock_ex_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != desc);
    RCPR_MODEL_ASSERT(NULL != addr);
    RCPR_MODEL_ASSERT(NULL != addrlen);
    RCPR_MODEL_ASSERT(*addrlen > 0);

    /* convert this to a psock_ex. */
    psock_ex* s = (psock_ex*)sock;

    /* call the user function if defined. */
    if (s->ex_accept_fn)
    {
        return s->ex_accept_fn(&s->hdr, s->ctx, desc, addr, addrlen);
    }
    else
    {
        return ERROR_PSOCK_USER_METHOD_UNDEFINED;
    }
}
