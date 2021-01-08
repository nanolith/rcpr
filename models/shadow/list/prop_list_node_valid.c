/**
 * \file models/shadow/psock/prop_list_node_valid.c
 *
 * \brief Check whether an list_node instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/list/list_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(list_node);

/**
 * \brief Valid \ref list_node property.
 *
 * \param node           The \ref list_node instance to be verified.
 *
 * \returns true if the \ref list_node instance is valid.
 */
bool prop_list_node_valid(const list_node* node)
{
    MODEL_ASSERT(NULL != node);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        node->MODEL_STRUCT_TAG_REF(list_node), list_node);

    MODEL_ASSERT(prop_resource_valid(&node->hdr));
    MODEL_ASSERT(prop_allocator_valid(node->alloc));

    return
        prop_resource_valid(&node->hdr)
     && prop_allocator_valid(node->alloc)
     && (    (node->parent != NULL && prop_list_valid(node->parent))
          || (node->parent == NULL && node->next == NULL))
     && (    (node->child != NULL && prop_resource_valid(node->child))
          || (node->child == NULL));
}
