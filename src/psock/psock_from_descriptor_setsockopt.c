/**
 * \file psock/psock_from_descriptor_setsockopt.c
 *
 * \brief Set a socket option for a psock from a descriptor.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <sys/socket.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Set a socket option for a \ref psock from descriptor socket instance.
 *
 * \param sock          The \ref psock instance for this setsockopt operation.
 * \param ctx           User context (ignored).
 * \param level         The protocol level at which this option resides.
 * \param option_name   The option to set.
 * \param option_value  The value to which this option is set.
 * \param option_len    The length of this option in bytes.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_setsockopt)(
    RCPR_SYM(psock)* sock, void* ctx, int level, int option_name,
    const void* option_value, socklen_t option_len)
{
    (void)ctx;
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != option_value);
    RCPR_MODEL_ASSERT(prop_valid_range(option_value, option_len));

    /* convert this to a psock_from_descriptor. */
    psock_from_descriptor* s = (psock_from_descriptor*)sock;

    /* attempt to set the socket option. */
    int retval =
        setsockopt(s->descriptor, level, option_name, option_value, option_len);
    if (retval < 0)
    {
        return ERROR_PSOCK_SETSOCKOPT;
    }

    /* success. */
    return STATUS_SUCCESS;
}
