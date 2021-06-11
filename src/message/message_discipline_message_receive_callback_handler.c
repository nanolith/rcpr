/**
 * \file message/message_discipline_message_receive_callback_handler.c
 *
 * \brief Handle a message receive request.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

/**
 * \brief The callback handler for a receive message request.
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
status message_discipline_message_receive_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    status retval;
    mailbox* mbox;
    mailbox_address addr;
    int resume_event;
    void* resume_param;

    /* ignore yield event. */
    (void)yield_event;

    /* get the message discipline context. */
    message_discipline_context* ctx = (message_discipline_context*)context;

    /* get the address. */
    addr = (mailbox_address)((ptrdiff_t)yield_param);

    /* look up the mailbox. */
    retval = rbtree_find((resource**)&mbox, ctx->mailboxes, &addr);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* mailbox sanity check. */
    MODEL_ASSERT(prop_mailbox_valid(mbox));

    /* if there are no messages to receive, block this fiber. */
    if (queue_count(mbox->message_queue) == 0)
    {
        /* if there is already a fiber blocking on this mailbox, return an
         * error. */
        if (NULL != mbox->blocked_fiber)
        {
            retval = ERROR_MESSAGE_ALREADY_BLOCKED;
            goto resume_fail;
        }

        /* otherwise, block the fiber and return successfully. */
        mbox->blocked_fiber = yield_fib;
        return STATUS_SUCCESS;
    }
    /* otherwise, give the next queue message to the fiber. */
    else
    {
        /* pop the first message off of the queue. */
        resource* msgresource;
        retval = queue_pop(mbox->message_queue, &msgresource);
        if (STATUS_SUCCESS != retval)
        {
            /* couldn't pop a message off of the queue. */
            resume_event =
                FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_FAILURE;
            resume_param = (void*)((ptrdiff_t)retval);
        }
        else
        {
            /* encode the popped message in the resume arguments. */
            resume_event =
                FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_SUCCESS;
            resume_param = msgresource;
        }

        /* resume the thread. */
        goto done;
    }

resume_fail:
    resume_event = FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_FAILURE;
    resume_param = (void*)((ptrdiff_t)retval);

done:
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE,
            resume_event, resume_param);
}
