/**
 * \file models/shadow/stack/stack_struct_tag_init.c
 *
 * \brief Initialize the stack struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/stack/stack_internal.h"

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(stack);

void stack_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(stack);
}
