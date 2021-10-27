/**
 * \file list/list_insert.c
 *
 * \brief Insert a resource before the given node in a list.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

RCPR_IMPORT_list;
RCPR_IMPORT_resource;

/**
 * \brief Insert the given \ref resource before the given \ref list_node.
 *
 * If there is already a previous node, then this \ref resource is placed
 * between the given \ref list_node and its previous node.
 *
 * \param node          Pointer to the \ref list_node to which the
 *                      \ref resource should be inserted.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the prev node of the provided
 * \ref list_node. The parent \ref list takes ownership of the \ref resource
 * pointed to by \p r and will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must be a valid \ref list_node assigned to a \ref list
 *        instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted before \p node in the \ref list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_insert)(
    RCPR_SYM(list_node)* node, RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_list_node_valid(node));
    RCPR_MODEL_ASSERT(prop_resource_valid(r));

    /* get the parent list. */
    list* parent = node->parent;
    RCPR_MODEL_ASSERT(prop_list_valid(parent));

    /* is there a previous node associated with node? */
    if (NULL != node->prev)
    {
        /* this is the same as append on node->prev. */
        return list_append(node->prev, r);
    }
    else
    {
        /* if there is no prev, then node is head, so list_insert_head. */
        return list_insert_head(parent, r);
    }
}
