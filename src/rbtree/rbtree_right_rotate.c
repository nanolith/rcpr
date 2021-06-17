/**
 * \file rbtree/rbtree_right_rotate.c
 *
 * \brief Perform a right rotate on a subtree of the given \ref rbtree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;

/**
 * \brief Perform a right rotation on a subtree in the given tree.
 *
 * \param tree          The \ref rbtree on which this operation is being
 *                      performed.
 * \param x             The pivot point node for this right rotation.
 */
void
RCPR_SYM(rbtree_right_rotate)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* y)
{
    MODEL_ASSERT(prop_rbtree_valid(tree));
    MODEL_ASSERT(prop_rbtree_node_valid(tree, y));

    /* from Cormen et al, 13.2. */

    /* set x. */
    rbtree_node* x = y->left;

    /* turn x's right subtree into y's left subtree. */
    y->left = x->right;

    /* set x->right's parent to y. */
    if (x->right != tree->nil)
    {
        x->right->parent = y;
    }

    /* link y's parent to x. */
    x->parent = y->parent;

    /* If y is root, set root to x. */
    if (y->parent == tree->nil)
    {
        tree->root = x;
    }
    /* otherwise, if y is the parent's right, set x to y's parent's right. */
    else if (y == y->parent->right)
    {
        y->parent->right = x;
    }
    /* By process of elimination, y is y's parent's left, so set x
     * accordingly. */
    else
    {
        y->parent->left = x;
    }

    /* put y on x's right. */
    x->right = y;

    /* x is now y's parent. */
    y->parent = x;
}
