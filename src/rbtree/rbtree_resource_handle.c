/**
 * \file rbtree/rbtree_resource_handle.c
 *
 * \brief Get the resource handle for an rbtree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;

/**
 * \brief Given a \ref rbtree instance, return the resource handle for this
 * \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(rbtree_resource_handle)(
    RCPR_SYM(rbtree)* tree)
{
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));

    return &(tree->hdr);
}
