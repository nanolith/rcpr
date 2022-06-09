/**
 * \file list/list_swap.c
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

#include "list_internal.h"

RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;

/**
 * \brief Swap the contents of two list instances.
 *
 * \param left          The left list instance for the swap.
 * \param right         The right list instance for the swap.
 *
 * \note This operation always succeeds, as long as \p left and \p right are
 * valid. If either are invalid, the result of this operation is unpredictable
 * and will likely crash.
 *
 * \pre
 *      - \p left must point to a valid \ref list instance.
 *      - \p right must point to a valid \ref list instance.
 * \post
 *      - \p left contains and owns the contents previously contained and owned
 *      by \p right.
 *      - \p right contains and owns the contents previously contained and owned
 *      by \p left.
 */
void RCPR_SYM(list_swap)(RCPR_SYM(list)* left, RCPR_SYM(list)* right)
{
    list tmp;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_list_valid(left));
    RCPR_MODEL_ASSERT(prop_list_valid(right));

    memcpy(&tmp, left, sizeof(tmp));
    memcpy(left, right, sizeof(tmp));
    memcpy(right, &tmp, sizeof(tmp));

    /* postcondition sanity checks. */
    RCPR_MODEL_ASSERT(prop_list_valid(left));
    RCPR_MODEL_ASSERT(prop_list_valid(right));
}
