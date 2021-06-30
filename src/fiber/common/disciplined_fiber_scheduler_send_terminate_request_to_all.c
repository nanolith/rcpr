/**
 * \file
 * fiber/common/disciplined_fiber_scheduler_send_terminate_request_to_all.c
 *
 * \brief Request that the disciplined scheduler send a quiesce request to all
 * fibers.
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
RCPR_IMPORT_uuid;

/**
 * \brief Tell the fiber scheduler to send a terminate request to all running
 *        fibers.
 *
 * \param sched         The scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, all running fibers have been instructed to terminate.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_send_terminate_request_to_all)(
    RCPR_SYM(fiber_scheduler)* sched)
{
    status retval;
    fiber_scheduler_disciplined_context* ctx = NULL;
    const rcpr_uuid* resume_id = NULL;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* Send this request to the management discipline. */
    retval =
        fiber_discipline_yield(
            ctx->management_discipline,
            FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_TERMINATION_REQUEST, NULL,
            &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* make sure this is the right resume id. */
    if (memcmp(resume_id, &FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE, 16)
     || FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_REQUEST_RESULT != resume_event)
    {
        return ERROR_FIBER_UNEXPECTED_RESUME_EVENT;
    }

    /* otherwise, the resume parameter is the result code. */
    retval = (status)(int64_t)resume_param;

    return retval;
}
