/**
 * \file fiber/common/disciplined_fiber_scheduler_idle_fiber_yield.c
 *
 * \brief Instruct the disciplined scheduler that the idle fiber wishes to
 * yield.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;

/**
 * \brief Suspend this idle fiber until the scheduler idles again.
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
 *      - On success, the fiber has been resumed normally.
 *      - On failure, either the yield failed or the fiber has been resumed due
 *        to an out-of-bound event.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_idle_fiber_yield)(
    RCPR_SYM(fiber_scheduler)* sched)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* we're just wrapping run.  The scheduler is smart enough to detect whether
     * this is the idle fiber. */
    return fiber_scheduler_run(sched);
}
