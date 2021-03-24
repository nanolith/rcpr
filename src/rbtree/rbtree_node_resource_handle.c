/**
 * \file rbtree/rbtree_node_resource_handle.c
 *
 * \brief Get the resource handle for an rbtree_node.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "rbtree_internal.h"

/**
 * \brief Given a \ref rbtree_node instance, return the resource handle for this
 * \ref rbtree_node instance.
 *
 * \param node          The \ref rbtree_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree_node instance.
 */
resource* rbtree_node_resource_handle(rbtree_node* node)
{
    return &node->hdr;
}
