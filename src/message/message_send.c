/**
 * \file message/message_send.c
 *
 * \brief Send a message using the messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_uuid;

/**
 * \brief Send a \ref message to the given mailbox.
 *
 * \param sendaddr      The \ref mailbox_address to which this message should be
 *                      sent.
 * \param msg           The \ref message to send to this address.
 * \param msgdisc       The messaging discipline.
 *
 * \note On success, the ownership of this \ref message is transferred to the
 * messaging discipline.  On failure, the ownership of this \ref message remains
 * with the caller.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(message_send)(
    RCPR_SYM(mailbox_address) sendaddr, RCPR_SYM(message)* msg,
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(sendaddr > 0);
    RCPR_MODEL_ASSERT(prop_message_valid(msg));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(msgdisc));

    /* set the send address. */
    msg->sendaddr = sendaddr;

    /* send the message. */
    retval =
        fiber_discipline_yield(
            msgdisc, FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MESSAGE_SEND, msg,
            &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    if (
        FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_SEND_FAILURE
            == resume_event)
    {
        retval = (status)(ptrdiff_t)resume_param;
        return retval;
    }
    else if (
        FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_SEND_SUCCESS
            == resume_event)
    {
        return STATUS_SUCCESS;
    }
    else
    {
        /* TODO - add support for out-of-band events. */
        return ERROR_MESSAGE_UNKNOWN_ERROR;
    }
}
