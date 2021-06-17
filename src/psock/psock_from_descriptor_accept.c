/**
 * \file psock/psock_from_descriptor_accept.c
 *
 * \brief Accept a socket from a listen descriptor.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <unistd.h>

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
status
RCPR_SYM(psock_from_descriptor_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(NULL != desc);
    MODEL_ASSERT(NULL != addr);
    MODEL_ASSERT(NULL != addrlen);
    MODEL_ASSERT(prop_valid_range(addr, *addrlen));

    /* convert this to a psock_from_descriptor. */
    psock_from_descriptor* s = (psock_from_descriptor*)sock;

    /* attempt to accept a socket. */
    int retval = accept(s->descriptor, addr, addrlen);
    if (retval < 0)
    {
        if (EAGAIN == errno || EWOULDBLOCK == errno)
        {
            return ERROR_PSOCK_ACCEPT_WOULD_BLOCK;
        }
        else
        {
            return ERROR_PSOCK_ACCEPT_GENERAL;
        }
    }

    /* success. */
    *desc = retval;
    return STATUS_SUCCESS;
}
