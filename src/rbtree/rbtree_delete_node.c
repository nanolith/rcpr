/**
 * \file rbtree/rbtree_delete_node.c
 *
 * \brief Delete a node from a red-black tree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Delete the given \ref rbtree_node from the \ref rbtree.
 *
 * \param tree          The \ref rbtree instance from which the node is deleted.
 * \param z             The \ref rbtree_node to delete from the tree.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero failure code on failure.
 */
status FN_DECL_MUST_CHECK
rbtree_delete_node(rbtree* tree, rbtree_node* z)
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

    /* finally, make sure that nil is correct. */
    tree->nil->parent = tree->nil;
    tree->nil->left = tree->nil;
    tree->nil->right = tree->nil;
    tree->nil->color = RBTREE_BLACK;

    return resource_release(rbtree_node_resource_handle(z));
}
