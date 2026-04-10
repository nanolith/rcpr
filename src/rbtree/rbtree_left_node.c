/**
 * \file rbtree/rbtree_left_node.c
 *
 * \brief Return the node to the left of the given node.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;

/**
 * \brief Return the node to the left of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The referenced \ref rbtree_node.
 *
 * \returns the node to the left of the referenced node, or tree->nil if none is
 * found.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_left_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x)
{
    (void)tree;

    return x->left;
}
