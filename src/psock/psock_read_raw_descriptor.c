/**
 * \file psock/psock_read_raw_descriptor.c
 *
 * \brief Read a file descriptor from a psock instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Read a SCM_RIGHTS message from the \ref psock instance, transferring
 * a copy of this open file descriptor from the peer to this process.
 *
 * \note This will only work for a Unix datagram socket, and this method will
 * verify the socket type.
 *
 * \param sock          Pointer to the \ref psock instance from which this
 *                      descriptor is read.
 * \param desc          Pointer to receive the descriptor on success.
 *
 * This method receives a duplicate an open descriptor from the peer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL. It must be a Unix domain datagram socket.
 *      - \p desc must be a valid pointer to an integer variable that will
 *        receive the descriptor.
 * \post
 *      - On success, \p desc is set to a descriptor that is owned by the caller
 *        and must be closed when no longer needed.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_descriptor)(
    RCPR_SYM(psock)* sock, int* desc)
{
    status retval;
    struct msghdr m;
    struct cmsghdr* cm;
    struct iovec iov;
    char dummy[100];
    char buf[CMSG_SPACE(sizeof(int))];
    size_t readlen;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(PSOCK_SOCKET_TYPE_DATAGRAM == sock->socktype);

    /* we can only work with datagram sockets. */
    if (PSOCK_SOCKET_TYPE_DATAGRAM != sock->socktype
     || NULL == sock->recvmsg_fn)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* set up the receive buffer. */
    iov.iov_base = dummy;
    iov.iov_len = sizeof(dummy);
    memset(&m, 0, sizeof(m));
    m.msg_iov = &iov;
    m.msg_iovlen = 1;
    m.msg_controllen = CMSG_SPACE(sizeof(int));
    m.msg_control = buf;

    /* set sentry for the receive socket. */
    *desc = -1;

    /* read a message from the socket. */
    retval = sock->recvmsg_fn(sock, &m, &readlen, 0);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* read the socket control messages from the parent. */
    for (cm = CMSG_FIRSTHDR(&m); NULL != cm; cm = CMSG_NXTHDR(&m, cm))
    {
        /* if this is a socket message, save the socket. */
        if (SOL_SOCKET == cm->cmsg_level && SCM_RIGHTS == cm->cmsg_type)
        {
            memcpy(desc, CMSG_DATA(cm), sizeof(int));
            break;
        }
    }

    /* verify that we received a socket. */
    if (*desc < 0)
    {
        return ERROR_PSOCK_READ_GENERAL;;
    }

    return STATUS_SUCCESS;
}
