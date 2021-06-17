/**
 * \file rbtree/rbtree_transplant.c
 *
 * \brief Transplant nodes in an \ref rbtree.
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
 * \brief Transplant moves subtrees around when a node with two children is
 * deleted.
 *
 * \param tree          The \ref rbtree instance on which the transplant is
 *                      occurring.
 * \param u             One node that is part of the transplant operation.
 * \param v             The other node that is part of the transplant operation.
 */
void
RCPR_SYM(rbtree_transplant)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* u, RCPR_SYM(rbtree_node)* v)
{
    if (u->parent == tree->nil)
    {
        tree->root = v;
    }
    else if (u == u->parent->left)
    {
        u->parent->left = v;
    }
    else
    {
        u->parent->right = v;
    }

    /* We are exploiting the fact that v may be tree->nil; the
     * rbtree_delete_fixup function assumes that v->parent is set to u->parent.
     * Later on, rbtree_delete will change tree->nil->parent back to tree->nil
     * as a final step to maintain tree->nil's purity.
     *
     * This is a hack, but this hack is in Cormen, and we will follow Cormen's
     * example.
     */
    v->parent = u->parent;
}
