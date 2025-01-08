/**
 * \file condition/condition_discipline_close_callback_handler.c
 *
 * \brief Handle a conditional close request.
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

/**
 * \brief The callback handler for a close conditional request.
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
status RCPR_SYM(condition_discipline_close_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval;
    int resume_event;
    void* resume_param;

    /* ignore yield event. */
    (void)yield_event;

    /* get the condition discipline context. */
    condition_discipline_context* ctx = (condition_discipline_context*)context;
    conditional cond = (conditional)((ptrdiff_t)yield_param);

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_condition_discipline_context_valid(ctx));
    RCPR_MODEL_ASSERT(cond > 0);

    /* Attempt to delete the condition barrier. */
    retval = rbtree_delete(NULL, ctx->condition_barriers, &cond);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* set the resume parameters on success. */
    resume_event = FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CLOSE_SUCCESS;
    resume_param = (void*)((ptrdiff_t)STATUS_SUCCESS);

    /* success. */
    goto done;

resume_fail:
    resume_event = FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CLOSE_FAILURE;
    resume_param = (void*)((ptrdiff_t)retval);

done:
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_CONDITION_DISCIPLINE,
            resume_event, resume_param);
}
