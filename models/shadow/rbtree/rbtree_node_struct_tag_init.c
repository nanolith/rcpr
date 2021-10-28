/**
 * \file models/shadow/rbtree/rbtree_node_struct_tag_init.c
 *
 * \brief Initialize the rbtree_node struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/rbtree/rbtree_internal.h"

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(rbtree_node);

void rbtree_node_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(rbtree_node);
}
