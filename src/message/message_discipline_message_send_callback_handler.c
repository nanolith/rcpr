/**
 * \file message/message_discipline_message_send_callback_handler.c
 *
 * \brief Handle a message send request.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_message_internal;
RCPR_IMPORT_queue;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

/**
 * \brief The callback handler for a send message request.
 *
 * \param context       Opaque pointer to the message discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_message_send_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval;
    mailbox* mbox;
    message* msg;
    mailbox_address addr;
    int resume_event;
    void* resume_param;

    /* ignore yield event. */
    (void)yield_event;

    /* get the message discipline context. */
    message_discipline_context* ctx = (message_discipline_context*)context;

    /* get the message. */
    msg = (message*)yield_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_message_discipline_context_valid(ctx));
    RCPR_MODEL_ASSERT(prop_message_valid(msg));

    /* get the address. */
    addr = msg->sendaddr;

    /* look up the mailbox. */
    retval = rbtree_find((resource**)&mbox, ctx->mailboxes, &addr);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* mailbox sanity check. */
    RCPR_MODEL_ASSERT(prop_mailbox_valid(mbox));

    /* append the message to the end of the mail queue. */
    retval = queue_append(mbox->message_queue, &msg->hdr);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* message sent, so tell the original fiber to restart. */
    retval =
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE,
            FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_SEND_SUCCESS, NULL);
    if (STATUS_SUCCESS != retval)
    {
        /* if there was a scheduling issue, let the scheduler know. */
        return retval;
    }

    /* if there is a blocked fiber on this mailbox, set it as the next fiber to
     * run. */
    if (NULL != mbox->blocked_fiber)
    {
        fiber* receive_fiber = mbox->blocked_fiber;
        mbox->blocked_fiber = NULL;

        /* pop the next message off of the queue. */
        resource* msgresource;
        retval = queue_pop(mbox->message_queue, &msgresource);
        if (STATUS_SUCCESS != retval)
        {
            resume_event =
                FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_FAILURE;
            resume_param = (void*)((ptrdiff_t)retval);
        }
        else
        {
            resume_event =
                FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_SUCCESS;
            resume_param = msgresource;
        }

        return
            disciplined_fiber_scheduler_set_next_fiber_to_run(
                ctx->sched, receive_fiber,
                &FIBER_SCHEDULER_MESSAGE_DISCIPLINE, resume_event,
                resume_param);
    }

resume_fail:
    resume_event = FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_SEND_FAILURE;
    resume_param = (void*)((ptrdiff_t)retval);

    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE,
            resume_event, resume_param);
}
