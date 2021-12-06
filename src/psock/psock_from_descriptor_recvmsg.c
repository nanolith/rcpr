/**
 * \file psock/psock_from_descriptor_recvmsg.c
 *
 * \brief Receive a message from the given \ref psock instance.
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
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_recvmsg)(
    RCPR_SYM(psock)* sock, struct msghdr* msg, size_t* len, int flags)
{
    ssize_t recvlen;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != msg);
    RCPR_MODEL_ASSERT(NULL != len);

    /* convert this to a psock_from_descriptor. */
    psock_from_descriptor* s = (psock_from_descriptor*)sock;

    /* attempt to receive a message. */
    recvlen = recvmsg(s->descriptor, msg, flags);
    if (recvlen < 0)
    {
        return ERROR_PSOCK_RECVMSG_FAILED;
    }

    /* success. */
    *len = (size_t)recvlen;
    return STATUS_SUCCESS;
}
