/**
 * \file slist/slist_count.c
 *
 * \brief Return the number of nodes in the list.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "slist_internal.h"

/**
 * \brief Get the count of nodes in an \ref slist.
 *
 * \param l             Pointer to the \ref slist under query.
 *
 * \returns the number of nodes in the given \ref slist.
 */
size_t
RCPR_SYM(slist_count)(
    RCPR_SYM(slist)* l)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_slist_valid(l));

    return l->count;
}
