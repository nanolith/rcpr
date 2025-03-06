/**
 * \file psock/psock_write_raw_descriptor.c
 *
 * \brief Write a file descriptor to a psock instance.
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
RCPR_IMPORT_resource;

/**
 * \brief Write a SCM_RIGHTS message to the \ref psock instance, transferring
 * an open file descriptor to the peer.
 *
 * \note This will only work for a Unix datagram socket, and this method will
 * verify the socket type.
 *
 * \param sock          Pointer to the \ref psock instance over which this
 *                      descriptor is sent.
 * \param desc          The descriptor to transfer.
 *
 * This method sends a duplicate an open descriptor to the peer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL. It must be a Unix domain datagram socket.
 *      - \p desc must be a valid file descriptor that can be transferred to the
 *        peer socket.
 * \post
 *      - On success, a new descriptor is given to the peer that is a duplicate
 *        of \p desc.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_descriptor)(
    RCPR_SYM(psock)* sock, int desc)
{
    status retval;
    struct msghdr m;
    struct cmsghdr* cm;
    struct iovec iov;
    char buf[CMSG_SPACE(sizeof(int))];
    char dummy[2];
    const psock_vtable* sock_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(PSOCK_SOCKET_TYPE_DATAGRAM == sock->socktype);

    /* get the socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&sock_vtable, psock_resource_handle(sock));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* We can only work with datagram sockets. */
    if (PSOCK_SOCKET_TYPE_DATAGRAM != sock->socktype
     || NULL == sock_vtable->sendmsg_fn)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* build the message header. */
    memset(&m, 0, sizeof(m));
    m.msg_controllen = CMSG_SPACE(sizeof(int));
    m.msg_control = &buf;
    memset(m.msg_control, 0, m.msg_controllen);

    /* build a socket control message header. */
    cm = CMSG_FIRSTHDR(&m);
    cm->cmsg_level = SOL_SOCKET;
    cm->cmsg_type = SCM_RIGHTS;
    cm->cmsg_len = CMSG_LEN(sizeof(int));
    memcpy(CMSG_DATA(cm), &desc, sizeof(int));
    m.msg_iov = &iov;
    m.msg_iovlen = 1;
    iov.iov_base = dummy;
    iov.iov_len = 1;
    memset(dummy, 0, sizeof(dummy));

    /* attempt to send this message to the peer. */
    retval = sock_vtable->sendmsg_fn(sock, sock->context, &m, 0);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* success. */
    return STATUS_SUCCESS;
}
