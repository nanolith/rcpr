/**
 * \file socket_utilities/socket_utility_socketpair.c
 *
 * \brief Utility function for creating a socket pair.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <unistd.h>

/**
 * \brief Create a socket pair, with the given domain, type, and protocol.
 *
 * \param domain            The domain for this socket pair.
 * \param type              The type of this socket pair.
 * \param protocol          The protocol for this socket pair.
 * \param left              A pointer to be set to the file descriptor for the
 *                          left side of this socket pair.
 * \param right             A pointer to be set to the file descriptor for the
 *                          right side of this socket pair.
 *
 * On success, left and right are set to the left and right sides of the created
 * socket pair.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_socketpair)(
    int domain, int type, int protocol, int* left, int* right)
{
    int sd[2];

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != left);
    MODEL_ASSERT(NULL != right);

    /* create the socket pair. */
    if (0 != socketpair(domain, type, protocol, sd))
    {
        return ERROR_SOCKET_UTILITIES_SOCKETPAIR_FAILURE;
    }

    /* assign the socket descriptors. */
    *left = sd[0];
    *right = sd[1];

    /* success. */
    return STATUS_SUCCESS;
}
