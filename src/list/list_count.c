/**
 * \file list/list_count.c
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

#include "list_internal.h"

/**
 * \brief Get the count of nodes in an \ref list.
 *
 * \param l             Pointer to the \ref list under query.
 *
 * \returns the number of nodes in the given \ref list.
 */
size_t list_count(list* l)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_list_valid(l));

    return l->count;
}