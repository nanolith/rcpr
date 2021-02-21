/**
 * \file models/shadow/fiber/fiber_struct_tag_init.c
 *
 * \brief Initialize the fiber struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/fiber/common/fiber_internal.h"

int MODEL_STRUCT_TAG_GLOBAL_REF(fiber);

void fiber_struct_tag_init()
{
    MODEL_STRUCT_TAG_GLOBAL_INIT(fiber);
}
