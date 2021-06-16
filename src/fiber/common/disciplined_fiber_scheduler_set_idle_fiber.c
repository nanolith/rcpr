/**
 * \file fiber/common/disciplined_fiber_scheduler_set_idle_fiber.c
 *
 * \brief Set the disciplined scheduler's idle fiber.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;

/**
 * \brief Set the following fiber as the idle fiber.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to set as the yield fiber.
 *
 * \note It is expected that the given fiber has already been added to the
 * scheduler previously. It is an error to add an unassociated fiber to the
 * scheduler in this way.  This fiber will be resumed with an idle event when
 * the run queue is empty.
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
 *      - On success, the scheduler will set the given fiber as its idle fiber.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_set_idle_fiber)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib)
{
    fiber_scheduler_disciplined_context* ctx = NULL;

    /* parameter sanity checking. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_fiber_valid(fib));
    MODEL_ASSERT(sched->disciplined);

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* set the idle fiber. */
    ctx->idle_fiber = fib;

    /* success. */
    return STATUS_SUCCESS;
}
