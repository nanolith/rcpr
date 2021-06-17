/**
 * \file rbtree/rbtree_successor_node.c
 *
 * \brief Return the successor node to a given node.
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
 * \brief Return the in-order successor node of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which a successor is found.
 *
 * \returns the successor node of this node, or tree->nil if none is found.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_successor_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x)
{
    if (x->right != tree->nil)
    {
        return rbtree_minimum_node(tree, x->right);
    }

    rbtree_node* y = x->parent;

    while (y != tree->nil && x == y->right)
    {
        x = y;
        y = y->parent;
    }

    return y;
}
