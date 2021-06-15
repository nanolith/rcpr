/**
 * \file fiber/common/fiber_scheduler_discipline_resource_handle.c
 *
 * \brief Return the fiber scheduler resource handle.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Given a \ref fiber_scheduler_discipline instance, return the resource
 * handle for this \ref fiber_scheduler_discipline instance.
 *
 * \param disc          The \ref fiber_scheduler_discipline instance from which
 *                      the resource handle is returned.
 *
 * \returns the \ref resource handle for this \ref fiber_scheduler_discipline
 *          instance.
 */
RCPR_SYM(resource)* fiber_scheduler_discipline_resource_handle(
    fiber_scheduler_discipline* disc)
{
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));

    return &disc->hdr;
}
