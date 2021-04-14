/**
 * \file rbtree/rbtree_insert_node.c
 *
 * \brief Insert a node into a red-black tree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Insert the given \ref rbtree_node into the \ref rbtree.
 *
 * After the completion of this call, the resource pointed to by \p z is owned
 * by the tree and will be released when it is released.
 *
 * \param tree          The \ref rbtree instance from which the node is removed.
 * \param z             The \ref rbtree_node to delete from the tree.
 */
void rbtree_insert_node(rbtree* tree, rbtree_node* z)
{
    rbtree_node* x = tree->root;
    rbtree_node* y = tree->nil;
    const void* z_key = tree->key(tree->context, z->value);

    while (x != tree->nil)
    {
        y = x;
        const void* x_key = tree->key(tree->context, x->value);

        int compare_result = tree->compare(tree->context, z_key, x_key);
        if (compare_result == RCPR_COMPARE_LT)
        {
            x = x->left;
        }
        else
        {
            x = x->right;
        }
    }

    z->parent = y;
    if (y == tree->nil)
    {
        tree->root = z;
    }
    else
    {
        const void* y_key = tree->key(tree->context, y->value);
        int compare_result = tree->compare(tree->context, z_key, y_key);

        if (compare_result == RCPR_COMPARE_LT)
        {
            y->left = z;
        }
        else
        {
            y->right = z;
        }
    }

    z->left = tree->nil;
    z->right = tree->nil;
    z->color = RBTREE_RED;

    rbtree_insert_fixup(tree, z);

    /* increment the count. */
    ++(tree->count);

    /* make sure that nil is correct. */
    tree->nil->parent = tree->nil;
    tree->nil->left = tree->nil;
    tree->nil->right = tree->nil;
    tree->nil->color = RBTREE_BLACK;
}
