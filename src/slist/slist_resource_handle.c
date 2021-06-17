/**
 * \file slist/slist_resource_handle.c
 *
 * \brief Get the resource handle for this list.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "slist_internal.h"

/**
 * \brief Given an \ref slist instance, return the resource handle for this
 * \ref slist instance.
 *
 * \param list          The \ref slist instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref slist instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(slist_resource_handle)(
    RCPR_SYM(slist)* list)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_slist_valid(list));

    /* return the resource handle for this list. */
    return &list->hdr;
}
