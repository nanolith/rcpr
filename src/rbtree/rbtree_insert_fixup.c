/**
 * \file rbtree/rbtree_insert_fixup.c
 *
 * \brief Perform a tree rebalancing fixup after insert.
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
 * \brief Perform a post-insert fixup of the given \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance to fix up.
 * \param z             The inserted node where the fixup starts.
 */
void
RCPR_SYM(rbtree_insert_fixup)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* z)
{
    while (RBTREE_RED == z->parent->color)
    {
        if (z->parent == z->parent->parent->left)
        {
            rbtree_node* y = z->parent->parent->right;

            if (RBTREE_RED == y->color)
            {
                z->parent->color = RBTREE_BLACK;
                y->color = RBTREE_BLACK;
                z->parent->parent->color = RBTREE_RED;
                z = z->parent->parent;
            }
            else
            {
                if (z == z->parent->right)
                {
                    z = z->parent;
                    rbtree_left_rotate(tree, z);
                }

                z->parent->color = RBTREE_BLACK;
                z->parent->parent->color = RBTREE_RED;
                rbtree_right_rotate(tree, z->parent->parent);
            }
        }
        else
        {
            rbtree_node* y = z->parent->parent->left;

            if (RBTREE_RED == y->color)
            {
                z->parent->color = RBTREE_BLACK;
                y->color = RBTREE_BLACK;
                z->parent->parent->color = RBTREE_RED;
                z = z->parent->parent;
            }
            else
            {
                if (z == z->parent->left)
                {
                    z = z->parent;
                    rbtree_right_rotate(tree, z);
                }

                z->parent->color = RBTREE_BLACK;
                z->parent->parent->color = RBTREE_RED;
                rbtree_left_rotate(tree, z->parent->parent);
            }
        }
    }

    tree->root->color = RBTREE_BLACK;
}
