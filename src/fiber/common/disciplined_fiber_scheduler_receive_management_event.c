/**
 * \file fiber/common/disciplined_fiber_scheduler_receive_management_event.c
 *
 * \brief Yield to the disciplined scheduler until a management event occurs.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stddef.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;

/**
 * \brief Suspend this fiber until a management event is received from the
 *        disciplined fiber scheduler, and then resume this fiber with that
 *        event.
 *
 * \param sched         The scheduler.
 * \param resume_id     Pointer to receive the event's discipline id.
 * \param resume_event  Pointer to receive the resume event for this fiber.
 * \param resume_param  Pointer to receive the resume parameter for this fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p resume_event is a valid pointer to an integer value.
 *      - \p resume_param is a valid pointer to a void pointer.
 *
 * \post
 *      - On success, the fiber has been resumed with a management event.
 *      - \p resume_event is set to the management event value.
 *      - \p resume_param is set to the management event parameter.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_receive_management_event)(
    RCPR_SYM(fiber_scheduler)* sched, const RCPR_SYM(rcpr_uuid)** resume_id,
    int* resume_event, void** resume_param)
{
    fiber_scheduler_disciplined_context* ctx = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(sched->disciplined);
    MODEL_ASSERT(NULL != resume_id);
    MODEL_ASSERT(NULL != resume_event);
    MODEL_ASSERT(NULL != resume_param);

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* Yield with the management discipline yield event to receive an event. */
    return
        fiber_discipline_yield(
            ctx->management_discipline,
            FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_RECEIVE_EVENT,
            NULL, resume_id, resume_event, resume_param);
}
