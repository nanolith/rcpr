/**
 * \file rbtree/rbtree_left_rotate.c
 *
 * \brief Perform a left rotate on a subtree of the given \ref rbtree.
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
 * \brief Perform a left rotation on a subtree in the given tree.
 *
 * \param tree          The \ref rbtree on which this operation is being
 *                      performed.
 * \param x             The pivot point node for this left rotation.
 */
void
RCPR_SYM(rbtree_left_rotate)(
    RCPR_SYM(rbtree)* tree,
    RCPR_SYM(rbtree_node)* x)
{
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));
    RCPR_MODEL_ASSERT(prop_rbtree_node_valid(tree, x));

    /* from Cormen et al, 13.2. */

    /* set y. */
    rbtree_node* y = x->right;

    /* turn y's left subtree into x's right subtree. */
    x->right = y->left;

    /* set y->left's parent to x. */
    if (y->left != tree->nil)
    {
        y->left->parent = x;
    }

    /* link x's parent to y. */
    y->parent = x->parent;

    /* If x is root, set root to y. */
    if (x->parent == tree->nil)
    {
        tree->root = y;
    }
    /* otherwise, if x is the parent's left, set y to x's parent's left. */
    else if (x == x->parent->left)
    {
        x->parent->left = y;
    }
    /* By process of elimination, x is x's parent's right, so set y
     * accordingly. */
    else
    {
        x->parent->right = y;
    }

    /* put x on y's left. */
    y->left = x;

    /* y is now x's parent. */
    x->parent = y;
}
