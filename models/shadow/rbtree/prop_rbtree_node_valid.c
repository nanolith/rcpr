/**
 * \file models/shadow/rbtree/prop_rbtree_node_valid.c
 *
 * \brief Check whether an rbtree_node instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(rbtree_node);

/**
 * \brief Valid \ref rbtree_node property.
 *
 * \param tree          The \ref rbtree instance to which this \ref rbtree_node
 *                      belongs.
 * \param node          The \ref rbtree_node instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool RCPR_SYM(prop_rbtree_node_valid)(
    const rbtree* tree, const rbtree_node* node)
{
    RCPR_MODEL_ASSERT(NULL != node);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        node->RCPR_MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);

    if (node->left != tree->nil)
    {
        RCPR_MODEL_ASSERT(prop_rbtree_node_valid(tree, node->left));
    }

    if (node->right != tree->nil)
    {
        RCPR_MODEL_ASSERT(prop_rbtree_node_valid(tree, node->right));
    }

    return
        prop_resource_valid(&node->hdr)
     && prop_resource_valid(node->value);
}
