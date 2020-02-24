/**
 * \file models/shadow/allocator/prop_allocator_valid.c
 *
 * \brief Check whether an allocator instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/allocator/allocator_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(allocator);

/**
 * \brief Valid allocator property.
 *
 * \param alloc         The allocator instance to be verified.
 *
 * \returns true if the allocator instance is valid.
 */
bool prop_allocator_valid(const allocator* alloc)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != alloc);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        alloc->MODEL_STRUCT_TAG_REF(allocator), allocator);

    return
           prop_resource_valid(allocator_resource_handle(alloc))
        && NULL != alloc->allocate_fn
        && NULL != alloc->reclaim_fn;
}
