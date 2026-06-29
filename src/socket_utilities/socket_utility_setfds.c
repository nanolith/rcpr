/**
 * \file socket_utilities/socket_utility_setfds.c
 *
 * \brief Map file descriptors to the given offsets.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>

/**
 * \brief Set the offsets of the given file descriptors to the provided mapped
 * values.
 *
 * \note This method should be called after \ref socket_utility_move_descriptors
 * in order to set custom descriptors to the expected values for a child
 * process. This variable length list of arguments should end with -1.
 *
 * \param curr          The first number in the pair is the current descriptor.
 * \param mapped        The second number in the pair is the offset to which
 *                      this descriptor should be mapped.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_setfds)(int curr, int mapped, ...)
{
    status retval;
    va_list args;

    va_start(args, mapped);
    retval = RCPR_SYM(vsocket_utility_setfds)(curr, mapped, args);
    va_end(args);

    return retval;
}
