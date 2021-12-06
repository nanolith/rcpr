/**
 * \file psock/psock_from_descriptor_sendmsg.c
 *
 * \brief Send a message over the given \ref psock instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_sendmsg)(
    RCPR_SYM(psock)* sock, const struct msghdr* msg, int flags)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != msg);

    /* convert this to a psock_from_descriptor. */
    psock_from_descriptor* s = (psock_from_descriptor*)sock;

    /* attempt to send a message. */
    if (sendmsg(s->descriptor, msg, flags) < 0)
    {
        return ERROR_PSOCK_SENDMSG_FAILED;
    }

    /* success. */
    return STATUS_SUCCESS;
}
