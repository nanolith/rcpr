/**
 * \file rbtree/rbtree_minimum_node.c
 *
 * \brief Return the minimum node in a given subtree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Return the minimum node in an rbtree subtree.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which the search should start.
 *
 * \returns the minimum node in this subtree.
 */
rbtree_node* rbtree_minimum_node(rbtree* tree, rbtree_node* x)
{
    while (x->left != tree->nil)
    {
        x = x->left;
    }

    return x;
}