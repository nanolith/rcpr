/**
 * \file allocator/allocator_resource_handle.c
 *
 * \brief Get the resource handle for a given allocator.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "allocator_internal.h"

/**
 * \brief Given an allocator instance, return the resource handle for this
 * allocator instance.
 *
 * \param alloc         The allocator instance from which the resource handle is
 *                      returned.
 *
 * \returns the resource handle for this allocator instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(allocator_resource_handle)(
    RCPR_SYM(allocator)* alloc)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != alloc);
    MODEL_ASSERT(prop_resource_valid(&alloc->hdr));

    return &alloc->hdr;
}
