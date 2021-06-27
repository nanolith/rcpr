/**
 * \file message/message_discipline_mailbox_create_callback_handler.c
 *
 * \brief Handle a mailbox create request.
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
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

/**
 * \brief The callback handler for a create mailbox request.
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
status RCPR_SYM(message_discipline_mailbox_create_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval, release_retval;
    mailbox* tmp;
    mailbox_address addr;
    int resume_event;
    void* resume_param;

    /* ignore yield event and yield parameter. */
    (void)yield_event;
    (void)yield_param;

    /* get the message discipline context. */
    message_discipline_context* ctx = (message_discipline_context*)context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_message_discipline_context_valid(ctx));

    /* compute the new address value. */
    addr = ctx->index + 1;

    /* attempt to create the new mailbox. */
    retval = mailbox_resource_create(&tmp, ctx->alloc, addr);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* insert the mailbox into the rbtree. */
    retval = rbtree_insert(ctx->mailboxes, &tmp->hdr);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mailbox;
    }

    /* increment the address on success. */
    ++ctx->index;

    /* set the resume parameters. */
    resume_event = FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CREATE_SUCCESS;
    resume_param = (void*)((ptrdiff_t)addr);

    /* success. */
    goto done;

cleanup_mailbox:
    release_retval = resource_release(&tmp->hdr);
    if (STATUS_SUCCESS != retval)
    {
        retval = release_retval;
    }

resume_fail:
    resume_event = FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CREATE_FAILURE;
    resume_param = (void*)((ptrdiff_t)retval);

done:
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE,
            resume_event, resume_param);
}
