/**
 * \file rbtree/rbtree_delete_fixup.c
 *
 * \brief Perform a tree rebalancing fixup after delete.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Perform a post-delete fixup of the given \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance to fix up.
 * \param x             The node now occupying the deleted node's position.
 */
void rbtree_delete_fixup(rbtree* tree, rbtree_node* x)
{
    while (x != tree->nil && x->color == RBTREE_BLACK)
    {
        if (x == x->parent->left)
        {
            rbtree_node* w = x->parent->right;

            if (w->color == RBTREE_RED)
            {
                w->color = RBTREE_BLACK;
                x->parent->color = RBTREE_RED;
                rbtree_left_rotate(tree, x->parent);
                w = x->parent->right;
            }

            if (    w->left->color == RBTREE_BLACK
                 && w->right->color == RBTREE_BLACK)
            {
                w->color = RBTREE_RED;
                x = x->parent;
            }
            else
            {
                if (w->right->color == RBTREE_BLACK)
                {
                    w->left->color = RBTREE_BLACK;
                    w->color = RBTREE_RED;
                    rbtree_right_rotate(tree, w);
                    w = x->parent->right;
                }

                w->color = x->parent->color;
                x->parent->color = RBTREE_BLACK;
                w->right->color = RBTREE_BLACK;
                rbtree_left_rotate(tree, x->parent);
                x = tree->root;
            }
        }
        else
        {
            rbtree_node* w = x->parent->left;

            if (x->color == RBTREE_RED)
            {
                w->color = RBTREE_BLACK;
                x->parent->color = RBTREE_RED;
                rbtree_right_rotate(tree, x->parent);
                w = x->parent->left;
            }

            if (    w->right->color == RBTREE_BLACK
                 && w->left->color == RBTREE_BLACK)
            {
                w->color = RBTREE_RED;
                x = x->parent;
            }
            else
            {
                if (w->left->color == RBTREE_BLACK)
                {
                    w->right->color = RBTREE_BLACK;
                    w->color = RBTREE_RED;
                    rbtree_left_rotate(tree, w);
                    w = x->parent->left;
                }

                w->color = x->parent->color;
                x->parent->color = RBTREE_BLACK;
                w->left->color = RBTREE_BLACK;
                rbtree_right_rotate(tree, x->parent);
                x = tree->root;
            }
        }
    }

    x->color = RBTREE_BLACK;
}
