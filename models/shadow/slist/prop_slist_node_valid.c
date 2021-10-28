/**
 * \file models/shadow/psock/prop_slist_node_valid.c
 *
 * \brief Check whether an slist_node instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/slist/slist_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(slist_node);

/**
 * \brief Valid \ref slist_node property.
 *
 * \param node           The \ref slist_node instance to be verified.
 *
 * \returns true if the \ref slist_node instance is valid.
 */
bool RCPR_SYM(prop_slist_node_valid)(const slist_node* node)
{
    RCPR_MODEL_ASSERT(NULL != node);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        node->RCPR_MODEL_STRUCT_TAG_REF(slist_node), slist_node);

    RCPR_MODEL_ASSERT(prop_resource_valid(&node->hdr));
    RCPR_MODEL_ASSERT(prop_allocator_valid(node->alloc));

    return
        prop_resource_valid(&node->hdr)
     && prop_allocator_valid(node->alloc)
     && (    (node->parent != NULL && prop_slist_valid(node->parent))
          || (node->parent == NULL && node->next == NULL))
     && (    (node->child != NULL && prop_resource_valid(node->child))
          || (node->child == NULL));
}
