/**
 * \file fiber/common/disciplined_fiber_scheduler_main_fiber_get.c
 *
 * \brief Get the main fiber from the disciplined scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Get the main fiber from the disciplined scheduler.
 *
 * \param fib           Pointer to the pointer to hold the main fiber.
 * \param sched         The scheduler.
 *
 * \note On success, the fiber's ownership remains with the scheduler. The main
 * fiber's lifetime matches the lifetime of the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p fib is a pointer to pointer to receive the main fiber. It must not
 *        be NULL.
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, \p fib is updated to point to the main fiber.
 */
status FN_DECL_MUST_CHECK
disciplined_fiber_scheduler_main_fiber_get(
    fiber** fib, fiber_scheduler* sched)
{
    fiber_scheduler_disciplined_context* ctx = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != fib);
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(sched->disciplined);

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* set the main fiber. */
    *fib = ctx->main_fiber;

    /* success. */
    return STATUS_SUCCESS;
}
