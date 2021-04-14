/**
 * \file rbtree/rbtree_remove_node.c
 *
 * \brief Remove a node from a red-black tree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Remove the given \ref rbtree_node from the \ref rbtree.
 *
 * After the completion of this call, the resource pointed to by \p z is owned
 * by the caller and must be released when no longer needed.
 *
 * \param tree          The \ref rbtree instance from which the node is removed.
 * \param z             The \ref rbtree_node to delete from the tree.
 */
void rbtree_remove_node(rbtree* tree, rbtree_node* z)
{
    rbtree_node* x;
    rbtree_node* y;

    y = z;
    bool y_original_color = y->color;

    if (z->left == tree->nil)
    {
        x = z->right;
        rbtree_transplant(tree, z, z->right);
    }
    else if (z->right == tree->nil)
    {
        x = z->left;
        rbtree_transplant(tree, z, z->left);
    }
    else
    {
        y = rbtree_minimum_node(tree, z->right);
        y_original_color = y->color;
        x = y->right;

        if (y->parent == z)
        {
            x->parent = y;
        }
        else
        {
            rbtree_transplant(tree, y, y->right);
            y->right = z->right;
            y->right->parent = y;
        }

        rbtree_transplant(tree, z, y);
        y->left = z->left;
        y->left->parent = y;
        y->color = z->color;
    }

    if (y_original_color == RBTREE_BLACK)
    {
        rbtree_delete_fixup(tree, x);
    }

    /* decrement the count. */
    --(tree->count);

    /* finally, make sure that nil is correct. */
    tree->nil->parent = tree->nil;
    tree->nil->left = tree->nil;
    tree->nil->right = tree->nil;
    tree->nil->color = RBTREE_BLACK;
}
