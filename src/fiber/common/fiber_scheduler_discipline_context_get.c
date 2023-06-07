/**
 * \file fiber/common/fiber_scheduler_discipline_context_get.c
 *
 * \brief Get the context associated with the given \ref
 * fiber_scheduler_discipline.
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
 * \brief Get the context associated with the given \ref
 * fiber_scheduler_discipline instance.
 *
 * \param disc          The discipline for this operation.
 *
 * \returns the context pointer provided when this discipline was created.
 */
void* RCPR_SYM(fiber_scheduler_discipline_context_get)(
    RCPR_SYM(fiber_scheduler_discipline)* disc)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));

    return disc->context;
}
