/**
 * \file socket_utilities/vsocket_utility_setfds.c
 *
 * \brief Map file descriptors to the given offsets.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>
#include <unistd.h>

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
 * \param args          The list of mapped pairs, terminated by -1.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(vsocket_utility_setfds)(int curr, int mapped, va_list args)
{
    status retval;
    int fd;

    /* loop through the pairs of descriptors */
    while (curr >= 0 && mapped >= 0)
    {
        /* map the file descriptor to the new place. */
        fd = dup2(curr, mapped);
        if (fd < 0)
        {
            retval = ERROR_SOCKET_UTILITIES_DUP2_FAILURE;
            goto done;
        }

        /* close the old fd. */
        close(curr);

        /* attempt to read the next descriptor. */
        curr = va_arg(args, int);
        if (curr < 0)
        {
            /* a negative number denotes the end of the list. */
            retval = STATUS_SUCCESS;
            goto done;
        }

        /* attempt to read the next mapped descriptor. */
        mapped = va_arg(args, int);
        if (mapped < 0)
        {
            /* the caller fenceposted the arguments. Error out. */
            retval = ERROR_GENERAL_INVALID_ARGUMENTS;
            goto done;
        }
    }

    /* if we get here, there was an issue with the argument parsing */
    retval = ERROR_GENERAL_INVALID_ARGUMENTS;
    goto done;

done:
    return retval;
}
