/**
 * \file models/shadow/fiber/prop_fiber_scheduler_valid.c
 *
 * \brief Check whether a fiber_scheduler instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber_scheduler);

/**
 * \brief Valid \ref fiber_scheduler property.
 *
 * \param sched         The \ref fiber_scheduler instance to be verified.
 *
 * \returns true if the \ref fiber_scheduler instance is valid.
 */
bool RCPR_SYM(prop_fiber_scheduler_valid)(const fiber_scheduler* sched)
{
    RCPR_MODEL_ASSERT(NULL != sched);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        sched->RCPR_MODEL_STRUCT_TAG_REF(fiber_scheduler), fiber_scheduler);

    return
        prop_resource_valid(&sched->hdr)
     && prop_allocator_valid(sched->alloc)
     && (       (NULL != sched->main_fiber
              && prop_fiber_valid(sched->main_fiber))
         ||     (NULL == sched->main_fiber))
     && NULL != sched->fn;
}
