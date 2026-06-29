/**
 * \file socket_utilities/socket_utility_close_other_fds.c
 *
 * \brief Close all file descriptors greater than the provided file descriptor.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>
#include <sys/select.h>
#include <unistd.h>

/**
 * \brief Close all file descriptors greater than the given descriptor.
 *
 * \param fd            Close any descriptor whose offset is greater than this
 *                      one.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_close_other_fds)(int fd)
{
    for (int i = fd + 1; i < FD_SETSIZE; ++i)
    {
        close(i);
    }

    return STATUS_SUCCESS;
}
