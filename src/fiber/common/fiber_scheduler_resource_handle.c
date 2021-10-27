/**
 * \file fiber/common/fiber_scheduler_resource_handle.c
 *
 * \brief Get the resource handle for a fiber_scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;

/**
 * \brief Given a \ref fiber_scheduler instance, return the resource handle for
 * this \ref fiber_scheduler instance.
 *
 * \param sched         The \ref fiber_scheduler instance from which the
 *                      resource handle is returned.
 *
 * \returns the \ref resource handle for this \ref fiber_scheduler instance.
 */
RCPR_SYM(resource)* RCPR_SYM(fiber_scheduler_resource_handle)(
    RCPR_SYM(fiber_scheduler)* sched)
{
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    return &(sched->hdr);
}
