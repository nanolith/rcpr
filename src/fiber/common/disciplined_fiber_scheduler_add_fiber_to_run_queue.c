/**
 * \file fiber/common/disciplined_fiber_scheduler_add_fiber_to_run_queue.c
 *
 * \brief Add a fiber to the run queue.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;
RCPR_IMPORT_queue;

/**
 * \brief Mark the given \ref fiber as runnable.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to mark as runnable.
 * \param resume_id     The resume event's discipline id.
 * \param resume_event  The resume event for this fiber.
 * \param resume_param  The resume parameter for this fiber.
 *
 * \note It is expected that the given fiber has already been added to the
 * scheduler previously. It is an error to add an unassociated fiber to the
 * scheduler in this way.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance, previously added
 *        to the given scheduler via \ref fiber_scheduler_add.
 *
 * \post
 *      - On success, the scheduler will add the given fiber to its run queue.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_add_fiber_to_run_queue)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib,
    const RCPR_SYM(rcpr_uuid)* resume_id, int resume_event, void* resume_param)
{
    fiber_scheduler_disciplined_context* ctx = NULL;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    RCPR_MODEL_ASSERT(prop_fiber_valid(fib));
    RCPR_MODEL_ASSERT(prop_uuid_valid(resume_id));
    RCPR_MODEL_ASSERT(sched->disciplined);

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* set the fiber resume parameters. */
    fib->restore_discipline_id = resume_id;
    fib->restore_reason_code = resume_event;
    fib->restore_param = resume_param;

    /* add this fiber to the run queue. */
    return queue_append(ctx->run_queue, fiber_resource_handle(fib));
}
