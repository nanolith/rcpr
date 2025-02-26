/**
 * \file psock/psock_from_buffer_accept.c
 *
 * \brief Accept a socket from a listen buffer.
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
 * \brief Dummy accept method.  We can't accept from a buffer.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param ctx           User context (ignored).
 * \param desc          Pointer to the integer field to hold the accepted
 *                      descriptor.
 * \param addr          The address of the accepted socket.
 * \param addrlen       On input, the max size of the address field; on output,
 *                      the size of the address field.
 *
 * \returns a status code indicating success or failure.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE - accept is unsupported in buffer socks.
 */
status RCPR_SYM(psock_from_buffer_accept)(
    RCPR_SYM(psock)* sock, void* ctx, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    (void)sock;
    (void)ctx;
    (void)desc;
    (void)addr;
    (void)addrlen;

    /* the accept operation is not supported. */
    return ERROR_PSOCK_UNSUPPORTED_TYPE;
}
