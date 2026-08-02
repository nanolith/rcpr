/**
 * \file psock/psock_create_socketpair.c
 *
 * \brief Create a linked pair of \ref psock instances.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

/**
 * \brief Create a pair of \ref psock instances backed by a connected pair of
 * sockets with the given domain, type, and protocol.
 *
 * \param lhs           Pointer to the \ref psock pointer to receive the
 *                      left-hand-side of this socket pair on success.
 * \param rhs           Pointer to the \ref psock pointer to receive the
 *                      right-hand-side of this socket pair on success.
 * \param a             Pointer to the allocator to use for creating this
 *                      socket pair.
 * \param domain        The domain for this socket pair.
 * \param type          The type of this socket pair.
 * \param protocol      The protocol for this socket pair.
 *
 * \note These \ref psock instances are both \ref resource instances that must
 * be released by calling \ref resource_release on their resource handles when
 * they are no longer needed by the caller.  The resource handle for these
 * instances can be accessed by calling \ref psock_resource_handle.
 *
 * The \ref psock instances created are assumed to be backed by a blocking
 * stream socket, and any read / write operations on these sockets will behave
 * accordingly.  On platforms which support this, \ref psock_create_wrap_async
 * can be called to wrap these \ref psock instances with an asynchronous I/O
 * instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a error code on failure.
 *
 * \pre
 *      - \p lhs must not reference a valid sock instance and must not be NULL.
 *      - \p rhs must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p domain must refer to a valid socket domain.
 *      - \p type must refer to a valid socket type.
 *      - \p protocol must refer to a valid protocol for this socket domain and
 *        type, or must be 0.
 *
 * \post
 *      - On success, \p lhs and \p rhs are set to pointers to valid \ref psock
 *        instances, which are \ref resource instances owned by the caller that
 *        must be released.
 *      - On failure, \p lhs and \p rhs are  set to NULL and an error status is
 *        returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_socketpair)(
    RCPR_SYM(psock)** lhs, RCPR_SYM(psock)** rhs, RCPR_SYM(allocator)* a,
    int domain, int type, int protocol)
{
    int retval, release_retval;
    int l = -1, r = -1;
    psock* tmp_lhs = NULL;
    psock* tmp_rhs = NULL;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != lhs);
    RCPR_MODEL_ASSERT(NULL != rhs);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));

    /* create the socketpair. */
    retval = socket_utility_socketpair(domain, type, protocol, &l, &r);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create a psock instance backed by the left-hand socket. */
    retval = psock_create_from_descriptor(&tmp_lhs, a, l);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_descriptors;
    }

    /* the left-hand descriptor is now owned by tmp_lhs. */
    l = -1;

    /* create a psock instance backed by the right-hand socket. */
    retval = psock_create_from_descriptor(&tmp_rhs, a, r);
    {
        goto cleanup_tmp_lhs;
    }

    /* the right-hand descriptor is now owned by tmp_rhs. */
    r = -1;

    /* success. */
    *lhs = tmp_lhs;
    *rhs = tmp_rhs;
    retval = STATUS_SUCCESS;
    goto done;

cleanup_tmp_lhs:
    release_retval = resource_release(psock_resource_handle(tmp_lhs));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_descriptors:
    if (l >= 0)
    {
        close(l);
    }

    if (r >= 0)
    {
        close(r);
    }

done:
    return retval;
}
