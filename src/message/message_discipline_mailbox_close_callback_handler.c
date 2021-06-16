/**
 * \file message/message_discipline_mailbox_close_callback_handler.c
 *
 * \brief Handle a mailbox close request.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_fiber;

/**
 * \brief The callback handler for a close mailbox request.
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
status message_discipline_mailbox_close_callback_handler(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval;
    int resume_event;
    void* resume_param;

    /* ignore yield event. */
    (void)yield_event;

    /* get the message discipline context. */
    message_discipline_context* ctx = (message_discipline_context*)context;
    mailbox_address addr = (mailbox_address)((ptrdiff_t)yield_param);

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_message_discipline_context_valid(ctx));
    MODEL_ASSERT(addr > 0);

    /* Attempt to delete the mailbox. */
    retval = rbtree_delete(NULL, ctx->mailboxes, &addr);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* set the resume parameters on success. */
    resume_event = FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CLOSE;
    resume_param = (void*)((ptrdiff_t)STATUS_SUCCESS);

    /* success. */
    goto done;

resume_fail:
    resume_event = FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CLOSE;
    resume_param = (void*)((ptrdiff_t)retval);

done:
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE,
            resume_event, resume_param);
}
