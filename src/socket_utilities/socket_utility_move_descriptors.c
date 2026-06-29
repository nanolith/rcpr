/**
 * \file socket_utilities/socket_utility_move_descriptors.c
 *
 * \brief Move descriptors to be equal to or greater than a threshold value.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>

/**
 * \brief Move the given list of file descriptors so they are equal to or above
 * a certain threshold.
 *
 * This operation updates the file descriptors with their new offsets.
 *
 * \param threshold             The threshold value for these descriptors; they
 *                              will be mapped to this value and above.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_move_descriptors)(int threshold, int* desc, ...)
{
    status retval;
    va_list args;

    va_start(args, desc);
    retval = RCPR_SYM(vsocket_utility_move_descriptors)(threshold, desc, args);
    va_end(args);

    return retval;
}
