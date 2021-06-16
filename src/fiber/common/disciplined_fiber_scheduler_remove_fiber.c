/**
 * \file fiber/common/disciplined_fiber_scheduler_remove_fiber.c
 *
 * \brief Remove a fiber from the disciplined fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_resource;

/**
 * \brief Remove the given fiber pointer from the disciplined fiber scheduler,
 *        transferring ownership to the caller.
 *
 * \param sched         The scheduler.
 * \param fib           Pointer to fiber to be removed from the scheduler.
 *
 * \note On success, the fiber's ownership is transferred to the caller, and the
 * caller is responsible for releasing the resource associated with this fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance currently owned by
 *        this scheduler.
 *
 * \post
 *      - On success, the fiber's ownership is transferred to the caller.
 */
status FN_DECL_MUST_CHECK
disciplined_fiber_scheduler_remove_fiber(
    fiber_scheduler* sched, fiber* fib)
{
    fiber_scheduler_disciplined_context* ctx = NULL;
    resource* tmp = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_fiber_valid(fib));
    MODEL_ASSERT(sched->disciplined);

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* remove the fiber. */
    return
        rbtree_delete(&tmp, ctx->fibers_by_pointer, fib);
}
