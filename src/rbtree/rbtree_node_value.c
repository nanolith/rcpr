/**
 * \file rbtree/rbtree_node_value.c
 *
 * \brief Return the value associated with the \ref rbtree_node.
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
 * \brief Return the value associated with a given rbtree node.
 *
 * \note Ownership of this value remains with the \ref rbtree_node.
 *
 * \param tree          The \ref rbtree instance.
 * \param node          The \ref rbtree_node accessed.
 *
 * \returns the resource associated with this node.
 */
RCPR_SYM(resource)*
RCPR_SYM(rbtree_node_value)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* node)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));
    RCPR_MODEL_ASSERT(prop_rbtree_node_valid(tree, node));

    /* the tree is unused by this function, but must be passed for model
     * checking. */
    (void)tree;

    return node->value;
}
