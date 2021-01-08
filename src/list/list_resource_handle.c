/**
 * \file list/list_resource_handle.c
 *
 * \brief Get the resource handle for this list.
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
 * \brief Given an \ref list instance, return the resource handle for this
 * \ref list instance.
 *
 * \param l             The \ref list instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref list instance.
 */
resource* list_resource_handle(list* l)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_list_valid(l));

    /* return the resource handle for this list. */
    return &l->hdr;
}
