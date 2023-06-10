/**
 * \file fiber/common/disciplined_fiber_scheduler_current_fiber_get.c
 *
 * \brief Get the current fiber from the disciplined scheduler.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;

/**
 * \brief Get the current fiber from the disciplined scheduler.
 *
 * \param fib           Pointer to the pointer to hold the current fiber.
 * \param sched         The scheduler.
 *
 * \note On success, the fiber's ownership remains with the scheduler. The
 * current fiber's lifetime matches the lifetime of the scheduler. Note that the
 * current fiber may change any time the fiber yields to the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p fib is a pointer to pointer to receive the current fiber. It must
 *        not be NULL.
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, \p fib is updated to point to the current fiber.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_current_fiber_get)(
    RCPR_SYM(fiber)** fib, RCPR_SYM(fiber_scheduler)* sched)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != fib);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    RCPR_MODEL_ASSERT(sched->disciplined);

    /* set the current fiber. */
    *fib = sched->current_fiber;

    /* success. */
    return STATUS_SUCCESS;
}
