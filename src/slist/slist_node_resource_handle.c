/**
 * \file slist/slist_node_resource_handle.c
 *
 * \brief Get the resource handle for this node.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
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
 * \brief Given an \ref slist_node instance, return the resource handle for this
 * \ref slist_node instance.
 *
 * \param node          The \ref slist_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref slist_node instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(slist_node_resource_handle)(
    RCPR_SYM(slist_node)* node)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_slist_node_valid(node));

    /* return the resource handle for this node. */
    return &node->hdr;
}
