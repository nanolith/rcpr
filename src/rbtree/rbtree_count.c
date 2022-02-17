/**
 * \file rbtree/rbtree_count.c
 *
 * \brief Get the number of elements currently in this rbtree instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;

/**
 * \brief Return the count of elements currently in this \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance.
 *
 * \returns the count of elements in the \ref rbtree instance.
 */
size_t
RCPR_SYM(rbtree_count)(
    RCPR_SYM(rbtree)* tree)
{
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));

    return tree->count;
}
