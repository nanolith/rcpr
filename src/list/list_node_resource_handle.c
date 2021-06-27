/**
 * \file list/list_node_resource_handle.c
 *
 * \brief Get the resource handle for this node.
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
 * \brief Given a \ref list_node instance, return the resource handle for this
 * \ref list_node instance.
 *
 * \param node          The \ref list_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref list_node instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(list_node_resource_handle)(
    RCPR_SYM(list_node)* node)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_list_node_valid(node));

    /* return the resource handle for this node. */
    return &node->hdr;
}
