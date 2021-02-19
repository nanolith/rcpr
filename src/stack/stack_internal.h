/**
 * \file stack/stack_internal.h
 *
 * \brief Internal data types and functions for stack.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/model_assert.h>
#include <rcpr/stack.h>
#include <unistd.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct stack
{
    resource hdr;

    MODEL_STRUCT_TAG(stack);

    allocator* alloc;
    void* region;
    size_t size;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
