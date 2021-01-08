/**
 * \file models/shadow/list/list_node_struct_tag_init.c
 *
 * \brief Initialize the list_node struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/list/list_internal.h"

int MODEL_STRUCT_TAG_GLOBAL_REF(list_node);

void list_node_struct_tag_init()
{
    MODEL_STRUCT_TAG_GLOBAL_INIT(list_node);
}
