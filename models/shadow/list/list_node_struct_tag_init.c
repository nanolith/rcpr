/**
 * \file models/shadow/list/list_node_struct_tag_init.c
 *
 * \brief Initialize the list_node struct tag.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "list_shadow.h"

RCPR_IMPORT_list;

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(list_node);

void list_node_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(list_node);
}
