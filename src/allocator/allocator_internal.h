/**
 * \file allocator/allocator_internal.h
 *
 * \brief Internal data types and functions for allocator.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(allocator)
{
    RCPR_SYM(resource) hdr;
    void* context;

    RCPR_MODEL_STRUCT_TAG(allocator);

    status (*allocate_fn)(
        RCPR_SYM(allocator* alloc), void** ptr, size_t size);
    status (*reclaim_fn)(
        RCPR_SYM(allocator* alloc), void* ptr);
    status (*reallocate_fn)(
        RCPR_SYM(allocator* alloc), void** ptr, size_t size);
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
