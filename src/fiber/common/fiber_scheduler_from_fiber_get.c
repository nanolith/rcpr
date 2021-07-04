/**
 * \file fiber/common/fiber_scheduler_from_fiber_get.c
 *
 * \brief Get the fiber's assigned scheduler.
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
 * \brief Given a \ref fiber instance, return the \ref fiber_scheduler assigned
 * to that instance.
 *
 * \param fib           The \ref fiber instance from which the 
 *                      \ref fiber_scheduler instance is returned.
 *
 * \returns the \ref fiber_scheduler instance assigned to this \ref fiber
 *          instance.
 */
RCPR_SYM(fiber_scheduler)*
RCPR_SYM(fiber_scheduler_from_fiber_get)(
    RCPR_SYM(fiber)* fib)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_valid(fib));

    return fib->sched;
}
