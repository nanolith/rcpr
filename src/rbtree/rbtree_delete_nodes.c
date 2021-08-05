/**
 * \file rbtree/rbtree_delete_nodes.c
 *
 * \brief Delete all nodes in this subtree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

/**
 * \brief Delete all nodes in this subtree, including this node.
 *
 * \param tree      The tree to which this subtree belongs.
 * \param n         The subtree to delete.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_delete_nodes)(
    rbtree* tree, rbtree_node* n)
{
    status retval_left = STATUS_SUCCESS;
    status retval_right = STATUS_SUCCESS;

    /* recursively delete the left branch. */
    if (tree->nil != n->left)
    {
        retval_left = rbtree_delete_nodes(tree, n->left);
    }

    /* recursively delete the right branch. */
    if (tree->nil != n->right)
    {
        retval_right = rbtree_delete_nodes(tree, n->right);
    }

    /* release this node. */
    status retval_node = resource_release(rbtree_node_resource_handle(n));

    /* if any operation failed, return a failure code. */
    if (STATUS_SUCCESS != retval_left)
        return retval_left;
    else if (STATUS_SUCCESS != retval_right)
        return retval_right;
    else if (STATUS_SUCCESS != retval_node)
        return retval_node;

    return STATUS_SUCCESS;
}
