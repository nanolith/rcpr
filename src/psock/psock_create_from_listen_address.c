/**
 * \file psock/psock_create_from_listen_address.c
 *
 * \brief Create a \ref psock instance from a listen address.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

/* forward decls. */
MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);

/**
 * \brief Create a \ref psock instance backed by a listen socket bound to the
 * given address.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param name          The name to which this socket should be bound.
 * \param namelen       The length of the name address field.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the descriptor, which will be closed when this resource is
 * released.
 *
 * The \ref psock instance created is assumed to be backed by a blocking stream
 * socket, and any read / write operations on this socket will behave
 * accordingly.  On platforms which support this, \ref psock_create_wrap_async
 * can be called to wrap this \ref psock instance with an asyncronous I/O
 * instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p descriptor must be a valid descriptor for a blocking socket stream.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
psock_create_from_listen_address(
    psock** sock, RCPR_SYM(allocator)* a, const struct sockaddr* name,
    socklen_t namelen)
{
    status retval;
    int res;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != sock);
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != name);
    MODEL_ASSERT(prop_valid_range(name, namelen));

    /* Create a socket for this address. */
    int desc = socket(AF_INET, SOCK_STREAM, 0);
    if (desc < 0)
    {
        retval = ERROR_PSOCK_CREATE_FROM_ADDRESS_SOCKET_CREATE;
        goto done;
    }

    /* bind this to the given address. */
    res = bind(desc, name, namelen);
    if (res < 0)
    {
        retval = ERROR_PSOCK_CREATE_FROM_ADDRESS_BIND;
        goto cleanup_socket;
    }

    /* start listening on this socket. */
    res = listen(desc, 32);
    if (res < 0)
    {
        retval = ERROR_PSOCK_CREATE_FROM_ADDRESS_LISTEN;
        goto cleanup_socket;
    }

    /* create the psock instance. */
    retval = psock_create_from_descriptor(sock, a, desc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_socket;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_socket:
    res = close(desc);
    if (res < 0)
    {
        retval = ERROR_PSOCK_CREATE_FROM_ADDRESS_CLOSE;
    }

done:
    return retval;
}
