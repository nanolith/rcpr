/**
 * \file psock/psock_create_from_hostname_and_port.c
 *
 * \brief Create a \ref psock instance using the given hostname and port.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <arpa/inet.h>
#include <netdb.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_psock;

/**
 * \brief Create a \ref psock instance connected to the peer address described
 * by the given hostname and port.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param hostname      The hostname for the connection.
 * \param port          The port.
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
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p hostname must be an ASCII UTF-8 ASCII-Z terminated string.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_from_hostname_and_port)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a,
    const char* hostname, unsigned int port)
{
    status retval;
    struct hostent* resolved;
    int desc;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != sock);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(NULL != hostname);

    /* attempt to resolve this as an IPv4 address. */
    resolved = gethostbyname2(hostname, AF_INET);
    if (NULL != resolved)
    {
        struct sockaddr_in addr;

        /* set the socket address family and port. */
        memset(&addr, 0, sizeof(addr));
        addr.sin_family = AF_INET;
        addr.sin_port = htons(port);
        memcpy(&addr.sin_addr, resolved->h_addr_list[0], resolved->h_length);

        /* create a socket. */
        desc = socket(AF_INET, SOCK_STREAM, 0);
        if (desc < 0)
        {
            retval = ERROR_PSOCK_SOCKET_CREATE;
            goto done;
        }

        /* attempt to connect to the given address using this socket. */
        retval = connect(desc, (struct sockaddr*)&addr, sizeof(addr));
        if (retval < 0)
        {
            retval = ERROR_PSOCK_CONNECTION_REFUSED;
            goto cleanup_desc;
        }
    }
    /* if IPv4 lookup fails, fall back to IPv6. */
    else
    {
        struct sockaddr_in6 addr;

        /* attempt to resolve this as an IPv6 address. */
        resolved = gethostbyname2(hostname, AF_INET6);
        if (NULL == resolved)
        {
            retval = ERROR_PSOCK_HOSTNAME_LOOKUP_FAILURE;
            goto done;
        }

        /* create a socket. */
        desc = socket(AF_INET6, SOCK_STREAM, 0);
        if (desc < 0)
        {
            retval = ERROR_PSOCK_SOCKET_CREATE;
            goto done;
        }

        /* set the socket address family and port. */
        memset(&addr, 0, sizeof(addr));
        addr.sin6_family = AF_INET6;
        addr.sin6_port = htons(port);
        memcpy(&addr.sin6_addr, resolved->h_addr_list[0], resolved->h_length);

        /* attempt to connect to the given address using this socket. */
        retval = connect(desc, (struct sockaddr*)&addr, sizeof(addr));
        if (retval < 0)
        {
            retval = ERROR_PSOCK_CONNECTION_REFUSED;
            goto cleanup_desc;
        }
    }

    /* turn this into a psock instance. */
    retval = psock_create_from_descriptor(sock, a, desc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_desc;
    }

    /* success. The psock instance owns the socket descriptor on success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_desc:
    close(desc);

done:
    return retval;
}
