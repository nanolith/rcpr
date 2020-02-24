/**
 * \file models/shadow/resource/resource_struct_tag_init.c
 *
 * \brief Initialize the resource struct tag.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/resource/resource_internal.h"

int MODEL_STRUCT_TAG_GLOBAL_REF(resource);

void resource_struct_tag_init()
{
    MODEL_STRUCT_TAG_GLOBAL_INIT(resource);
}
