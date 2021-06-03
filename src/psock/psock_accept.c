/**
 * \file psock/psock_accept.c
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

/**
 * \brief Accept a socket from a listen socket \ref psock instance.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param desc          Pointer to the integer variable to receive the socket
 *                      descriptor.
 * \param addr          Pointer to a socket address structure to receive the
 *                      peer's address.
 * \param addrlen       Pointer to a size for the socket address, which will be
 *                      updated with the size of socket address from this accept
 *                      operation.
 *
 * This method accepts a socket from a bound listen socket, created with
 * \ref psock_create_from_listen_address.  This socket is from a peer who
 * connected to the address and port specified by that constructor.  This
 * descriptor is a RAW RESOURCE that is not yet backed by a resource.  It must
 * be closed via \ref close or passed to \ref psock_create_from_descriptor to
 * turn it into a proper \ref resource.  The reason for making this a RAW
 * RESOURCE is historic and based on existing socket programming patterns.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p desc must be a pointer to a valid integer variable and must not be
 *        NULL.
 *      - \p addr must be a pointer to a socket address structure and must not
 *        be NULL.
 *      - \p addrlen must be a pointer to a socket length field set to the size
 *        of \p addr and must not be NULL.
 * \post
 *      - on success, \p desc is set to a socket descriptor that must either be
 *        closed or attached to a psock instance.
 *      - on success, \p addr and \p addrlen are set to the peer's address.
 *      - on failure, no field is updated.
 */
status FN_DECL_MUST_CHECK
psock_accept(
    psock* sock, int* desc, struct sockaddr* addr, socklen_t* addrlen)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(NULL != desc);
    MODEL_ASSERT(NULL != addr);
    MODEL_ASSERT(NULL != addrlen);
    MODEL_ASSERT(*addrlen > 0);

    return
        sock->accept_fn(sock, desc, addr, addrlen);
}
