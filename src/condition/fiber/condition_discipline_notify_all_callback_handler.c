/**
 * \file condition/condition_discipline_notify_all_callback_handler.c
 *
 * \brief Handle a conditional notify all request.
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
 * \brief The callback handler for a conditional notify all request.
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
status RCPR_SYM(condition_discipline_notify_all_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    status retval;
    condition_barrier* cond;
    conditional handle;
    int resume_event;
    void* resume_param;

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

    /* for every waiting fiber... */
    while (slist_count(cond->wait_list) > 0)
    {
        /* get a waiting fiber. */
        fiber* fib;
        retval = slist_pop(cond->wait_list, (resource**)&fib);
        if (STATUS_SUCCESS != retval)
        {
            /* skip failures. */
            continue;
        }

        /* resume the waiting fiber. */
        retval =
            disciplined_fiber_scheduler_add_fiber_to_run_queue(
                ctx->sched, fib, &FIBER_SCHEDULER_CONDITION_DISCIPLINE,
                FIBER_SCHEDULER_CONDITION_RESUME_EVENT_WAIT_SUCCESS,
                (void*)((ptrdiff_t)STATUS_SUCCESS));
        if (STATUS_SUCCESS != retval)
        {
            /* skip failures. */
            continue;
        }
    }

    /* success. */
    goto resume_success;

resume_fail:
    resume_event = FIBER_SCHEDULER_CONDITION_RESUME_EVENT_NOTIFY_FAILURE;
    resume_param = (void*)((ptrdiff_t)retval);
    goto done;

resume_success:
    resume_event = FIBER_SCHEDULER_CONDITION_RESUME_EVENT_NOTIFY_SUCCESS;
    resume_param = (void*)((ptrdiff_t)retval);
    goto done;

done:
    return
        disciplined_fiber_scheduler_add_fiber_to_run_queue(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_CONDITION_DISCIPLINE,
            resume_event, resume_param);
}
