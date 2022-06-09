/**
 * \file rbtree/rbtree_swap.c
 *
 * \brief Swap the contents of two rbtree instances.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;

/**
 * \brief Swap the contents of two rbtree instances.
 *
 * \param left          The left rbtree instance for the swap.
 * \param right         The right rbtree instance for the swap.
 *
 * \note This operation always succeeds, as long as \p left and \p right are
 * valid. If either are invalid, the result of this operation is unpredictable
 * and will likely crash.
 *
 * \pre
 *      - \p left must point to a valid \ref rbtree instance.
 *      - \p right must point to a valid \ref rbtree instance.
 * \post
 *      - \p left contains and owns the contents previously contained and owned
 *      by \p right
 *      - \p right contains and owns the contents previously contained and owned
 *      by \p left.
 */
void RCPR_SYM(rbtree_swap)(RCPR_SYM(rbtree)* left, RCPR_SYM(rbtree)* right)
{
    rbtree tmp;

    /* precondition sanity checks. */
    RCPR_MODEL_ASSERT(prop_rbtree_valid(left));
    RCPR_MODEL_ASSERT(prop_rbtree_valid(right));

    memcpy(&tmp, left, sizeof(tmp));
    memcpy(left, right, sizeof(tmp));
    memcpy(right, &tmp, sizeof(tmp));

    /* postcondition sanity checks. */
    RCPR_MODEL_ASSERT(prop_rbtree_valid(left));
    RCPR_MODEL_ASSERT(prop_rbtree_valid(right));
}
