/**
 * \file socket_utilities/socket_utility_close_standard_fds.c
 *
 * \brief Utility function for closing standard file descriptors.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>
#include <unistd.h>

/**
 * \brief Close standard file descriptors, such as standard input, standard
 * output, and standard error.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_close_standard_fds)(void)
{
    close(STDIN_FILENO);
    close(STDOUT_FILENO);
    close(STDERR_FILENO);

    return STATUS_SUCCESS;
}
