/**
 * \file models/shadow/list/property_list_node_valid.c
 *
 * \brief Check whether a list_node instance is valid.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "list_shadow.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(list_node);

/**
 * \brief Valid \ref list_node property.
 *
 * \param node          The \ref list_node instance to be verified.
 *
 * \returns true if the \ref list_node instance is valid.
 */
bool
RCPR_SYM(property_list_node_valid)(const RCPR_SYM(list_node)* node)
{
    RCPR_MODEL_CHECK_OBJECT_READ(node, sizeof(*node));
    RCPR_MODEL_CHECK_OBJECT_READ(node->parent, sizeof(*node->parent));
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        node->RCPR_MODEL_STRUCT_TAG_REF(list_node), list_node);

    RCPR_MODEL_ASSERT(prop_resource_valid(&node->hdr));
    RCPR_MODEL_ASSERT(property_allocator_valid(node->alloc));

    if (NULL != node->child)
    {
        RCPR_MODEL_ASSERT(prop_resource_valid(node->child));
    }

    return true;
}
