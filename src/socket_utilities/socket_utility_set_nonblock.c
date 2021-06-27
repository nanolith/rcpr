/**
 * \file socket_utilities/socket_utility_set_nonblock.c
 *
 * \brief Utility function for setting a descriptor to non-blocking.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <sys/fcntl.h>

/**
 * \brief Set a descriptor to non-blocking.
 *
 * \param desc              The descriptor to set to non-blocking.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_set_nonblock)(
    int desc)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(desc >= 0);

    /* get the flags for this descriptor. */
    int flags = fcntl(desc, F_GETFL);
    if (flags < 0)
    {
        return ERROR_SOCKET_UTILITIES_SET_NONBLOCK_FAILURE;
    }

    /* set the non-blocking bit. */
    flags |= O_NONBLOCK;

    /* set the flags for this descriptor. */
    int retval = fcntl(desc, F_SETFL, flags);
    if (retval < 0)
    {
        return ERROR_SOCKET_UTILITIES_SET_NONBLOCK_FAILURE;
    }

    /* success. */
    return STATUS_SUCCESS;
}
