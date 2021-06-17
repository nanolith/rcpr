/**
 * \file slist/slist_append_tail.c
 *
 * \brief Append a resource to the tail of an \ref slist.
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
 * \brief Append the given \ref resource to the next value of the given \ref
 * slist_node.
 *
 * If there is already a next node, then this \ref resource is placed between
 * the given \ref slist_node and its next node.
 *
 * \param node          Pointer to the \ref slist_node to which the
 *                      \ref resource should be appended.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref slist_node will be created to hold the
 * given \ref resource, and this node will become the next node of the provided
 * \ref slist_node. The parent \ref slist takes ownership of the \ref resource
 * pointed to by \p r and will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must be a valid \ref slist_node assigned to a \ref slist
 *        instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended to the end of \p list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_append)(
    RCPR_SYM(slist_node)* node, RCPR_SYM(resource)* r)
{
    slist_node* new_node;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_slist_node_valid(node));
    MODEL_ASSERT(prop_resource_valid(r));

    /* get the parent list. */
    slist* parent = node->parent;
    MODEL_ASSERT(prop_slist_valid(parent));

    /* attempt to create an slist_node. */
    int retval = slist_node_create(&new_node, node->parent, r);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* is this node the tail? */
    if (node == parent->tail)
    {
        /* set the new node to the tail. */
        parent->tail = new_node;
    }

    /* set new_node's next to node's next. */
    new_node->next = node->next;

    /* set node's next to new_node. */
    node->next = new_node;

    /* increment the count. */
    ++parent->count;

    /* success. */
    return STATUS_SUCCESS;
}
