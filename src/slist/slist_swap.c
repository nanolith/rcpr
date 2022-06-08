/**
 * \file slist/slist_swap.c
 *
 * \brief Swap the contents of two lists.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "slist_internal.h"

RCPR_IMPORT_slist;
RCPR_IMPORT_slist_internal;

/**
 * \brief Swap the contents of two slist instances.
 *
 * \param left          The left slist instance for the swap.
 * \param right         The right slist instance for the swap.
 *
 * \note This operation always succeeds, as long as \p left and \p right are
 * valid. If either are invalid, the result of this operation is unpredictable
 * and will likely crash.
 *
 * \pre
 *      - \p left must point to a valid \ref slist instance.
 *      - \p right must point to a valid \ref slist instance.
 * \post
 *      - \p left contains and owns the contents previously contained and owned
 *      by \p right.
 *      - \p right contains and owns the contents previously contained and owned
 *      by \p left.
 */
void RCPR_SYM(slist_swap)(RCPR_SYM(slist)* left, RCPR_SYM(slist)* right)
{
    slist tmp;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_slist_valid(left));
    RCPR_MODEL_ASSERT(prop_slist_valid(right));

    memcpy(&tmp, left, sizeof(tmp));
    memcpy(left, right, sizeof(tmp));
    memcpy(right, &tmp, sizeof(tmp));

    /* postcondition sanity checks. */
    RCPR_MODEL_ASSERT(prop_slist_valid(left));
    RCPR_MODEL_ASSERT(prop_slist_valid(right));
}
