/**
 * \file rbtree/rbtree_predecessor_node.c
 *
 * \brief Return the predecessor node to a given node.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Return the in-order predecessor node of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which a predecessor is found.
 *
 * \returns the predecessor node of this node, or tree->nil if none is found.
 */
rbtree_node* rbtree_predecessor_node(rbtree* tree, rbtree_node* x)
{
    if (x->left != tree->nil)
    {
        return rbtree_maximum_node(tree, x->left);
    }

    rbtree_node* y = x->parent;

    while (y != tree->nil && x == y->left)
    {
        x = y;
        y = y->parent;
    }

    return y;
}
