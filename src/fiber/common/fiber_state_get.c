/**
 * \file fiber/common/fiber_state_get.c
 *
 * \brief Get the fiber's state.
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
 * \brief Given a \ref fiber instance, return its current state.
 *
 * \param fib           The \ref fiber instance.
 *
 * \returns the fiber state, one of the values in the \ref fiber_state
 * enumeration.
 */
uint64_t RCPR_SYM(fiber_state_get)(const RCPR_SYM(fiber)* fib)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_valid(fib));

    return fib->fiber_state;
}
