/**
 * \file models/shadow/slist/slist_node_struct_tag_init.c
 *
 * \brief Initialize the slist_node struct tag.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/slist/slist_internal.h"

int MODEL_STRUCT_TAG_GLOBAL_REF(slist_node);

void slist_node_struct_tag_init()
{
    MODEL_STRUCT_TAG_GLOBAL_INIT(slist_node);
}
