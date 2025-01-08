/**
 * \file condition/condition_discipline_mailbox_create_callback_handler.c
 *
 * \brief Handle a conditional create request.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "../condition_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_condition;
RCPR_IMPORT_condition_internal;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

/**
 * \brief The callback handler for a create conditional request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_create_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval, release_retval;
    condition_barrier* tmp;
    conditional cond;
    int resume_event;
    void* resume_param;

    /* ignore yield event and yield parameter. */
    (void)yield_event;
    (void)yield_param;

    /* get the condition discipline context. */
    condition_discipline_context* ctx = (condition_discipline_context*)context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_condition_discipline_context_valid(ctx));

    /* compute the new address value. */
    cond = ctx->index + 1;

    /* attempt to create the new mailbox. */
    retval = condition_barrier_create(&tmp, ctx->alloc, cond);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* insert the condition barrier into the rbtree. */
    retval = rbtree_insert(ctx->condition_barriers, &tmp->hdr);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_condition_barrier;
    }

    /* increment the address on success. */
    ++ctx->index;

    /* set the resume parameters. */
    resume_event = FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CREATE_SUCCESS;
    resume_param = (void*)((ptrdiff_t)cond);

    /* success. */
    goto done;

cleanup_condition_barrier:
    release_retval = resource_release(&tmp->hdr);
    if (STATUS_SUCCESS != retval)
    {
        retval = release_retval;
    }

resume_fail:
    resume_event = FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CREATE_FAILURE;
    resume_param = (void*)((ptrdiff_t)retval);

done:
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_CONDITION_DISCIPLINE,
            resume_event, resume_param);
}
