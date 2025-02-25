/**
 * \file condition/condition_discipline_wait_callback_handler.c
 *
 * \brief Handle a conditional wait request.
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
RCPR_IMPORT_slist;

/**
 * \brief The callback handler for a conditional wait request.
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
status RCPR_SYM(condition_discipline_wait_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval;
    condition_barrier* cond;
    conditional handle;

    /* ignore yield event. */
    (void)yield_event;

    /* get the condition discipline context. */
    condition_discipline_context* ctx = (condition_discipline_context*)context;

    /* get the handle. */
    handle = (conditional)((ptrdiff_t)yield_param);

    /* look up the condition barrier. */
    retval = rbtree_find((resource**)&cond, ctx->condition_barriers, &handle);
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* condition barrier sanity check. */
    RCPR_MODEL_ASSERT(prop_condition_barrier_valid(cond));

    /* add this fiber to the wait list. */
    retval =
        slist_append_tail(cond->wait_list, fiber_resource_handle(yield_fib));
    if (STATUS_SUCCESS != retval)
    {
        goto resume_fail;
    }

    /* success. */
    return STATUS_SUCCESS;

resume_fail:
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_CONDITION_DISCIPLINE,
            FIBER_SCHEDULER_CONDITION_RESUME_EVENT_WAIT_FAILURE,
            (void*)((ptrdiff_t)retval));
}
