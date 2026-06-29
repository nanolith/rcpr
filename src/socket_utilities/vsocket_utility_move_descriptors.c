/**
 * \file socket_utilities/vsocket_utility_move_descriptors.c
 *
 * \brief Move descriptors to be equal to or greater than a threshold value.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/socket_utilities.h>
#include <stddef.h>
#include <unistd.h>

/**
 * \brief Move the given list of file descriptors so they are equal to or above
 * a certain threshold.
 *
 * This operation updates the file descriptors with their new offsets.
 *
 * \param threshold             The threshold value for these descriptors; they
 *                              will be mapped to this value and above.
 * \param desc                  Pointer to the first descriptor.
 * \param args                  The list of remaining args, terminated by NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(vsocket_utility_move_descriptors)(
    int threshold, int* desc, va_list args)
{
    status retval;
    int* curr;

    /* runtime parameter checks. */
    if (threshold < 0)
    {
        return ERROR_GENERAL_INVALID_ARGUMENTS;
    }

    /* Process each descriptor in the list */
    curr = desc;
    while (NULL != curr)
    {
        int new_fd;
        int old_fd = *curr;

        /* Check if the descriptor is valid */
        if (old_fd < 0)
        {
            retval = ERROR_GENERAL_INVALID_ARGUMENTS;
            goto done;
        }

        /* Move the descriptor to the threshold or above */
        new_fd = dup2(old_fd, threshold);
        if (new_fd < 0)
        {
            retval = ERROR_SOCKET_UTILITIES_DUP2_FAILURE;
            goto done;
        }

        /* Close the old file descriptor */
        close(old_fd);

        /* Update the descriptor to point to the new location */
        *curr = threshold;

        /* Advance to next descriptor */
        curr = va_arg(args, int*);
        threshold++;
    }

    retval = STATUS_SUCCESS;

done:
    return retval;
}
