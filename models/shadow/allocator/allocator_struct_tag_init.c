/**
 * \file models/shadow/allocator/allocator_struct_tag_init.c
 *
 * \brief Initialize the allocator struct tag.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/allocator/allocator_internal.h"

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(allocator);

void allocator_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(allocator);
}
