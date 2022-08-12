/**
 * \file rbtree/rbtree_clear.c
 *
 * \brief Clear all entries from an rbtree instance, releasing resources held by
 * all nodes.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

/**
 * \brief Clear all entries from an rbtree instance, releasing resources held by
 * all nodes.
 *
 * \param tree          Pointer to the \ref rbtree for the clear operation.
 *
 * \note After a successful clear, all resources associated with nodes in this
 * \ref rbtree instance are released.  All nodes are pruned.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *
 * \post
 *      - On success, all nodes in \p tree as well as all resources held by
 *        those nodes are released.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_clear)(
    RCPR_SYM(rbtree)* tree)
{
    status retval = STATUS_SUCCESS;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));

    /* delete all nodes in the tree if the tree is not empty. */
    if (tree->root != tree->nil)
    {
        retval = rbtree_delete_nodes(tree, tree->root);
    }

    /* now the tree is empty. */
    tree->root = tree->nil;
    tree->count = 0;

    /* make sure that nil is correct. */
    tree->nil->parent = tree->nil;
    tree->nil->left = tree->nil;
    tree->nil->right = tree->nil;
    tree->nil->color = RBTREE_BLACK;

    return retval;
}
