/**
 * \file rbtree/rbtree_root_node.c
 *
 * \brief Return the root node for the given tree.
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
 * \brief Return the root node pointer for the tree.
 *
 * \param tree          The \ref rbtree instance.
 *
 * \returns the root pointer for this tree.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_root_node)(
    RCPR_SYM(rbtree)* tree)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));

    return tree->root;
}
