/**
 * \file message/message_receive.c
 *
 * \brief Receive a message using the messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_uuid;

/**
 * \brief Receive a \ref message from the mailbox.
 *
 * \param recvaddr      The \ref mailbox_address from which a message should be
 *                      received.
 * \param msg           Pointer to a \ref message pointer to receive a message.
 * \param msgdisc       The messaging discipline.
 *
 * \note This call blocks until a message is available to receive, or until this
 * call is interrupted by an out-of-bound event.  On success, a \ref message is
 * available in \p msg.  This message is a resource that is owned by the caller
 * and must be released by calling \ref resource_release on its resource handle.
 * The resource handle for this \ref message can be obtained by calling
 * \ref message_resource_handle.  On failure, \p msg does not contain a valid
 * message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(message_receive)(
    RCPR_SYM(mailbox_address) recvaddr, RCPR_SYM(message)** msg,
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(recvaddr > 0);
    RCPR_MODEL_ASSERT(NULL != msg);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(msgdisc));

    /* receive a message. */
    retval =
        fiber_discipline_yield(
            msgdisc, FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MESSAGE_RECEIVE,
            (void*)recvaddr, &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* if the resume event is MESSAGE_RECEIVE_FAILURE, return the error. */
    if (
        FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_FAILURE
            == resume_event)
    {
        retval = (status)(ptrdiff_t)resume_param;
        return retval;
    }
    else if (
        FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_SUCCESS
            == resume_event)
    {
        /* on success, resume_param is our received message. */
        *msg = (message*)resume_param;

        return STATUS_SUCCESS;
    }
    else
    {
        /* TODO - add support for out-of-band events. */

        return ERROR_MESSAGE_UNKNOWN_ERROR;
    }
}
