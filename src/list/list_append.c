/**
 * \file list/list_append_tail.c
 *
 * \brief Append a resource to the tail of an \ref list.
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
 * \brief Append the given \ref resource to the next value of the given \ref
 * list_node.
 *
 * If there is already a next node, then this \ref resource is placed between
 * the given \ref list_node and its next node.
 *
 * \param node          Pointer to the \ref list_node to which the
 *                      \ref resource should be appended.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the next node of the provided
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
 *      - On success, \p r is appended after \p node in the \ref list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
list_append(
    list_node* node, resource* r)
{
    list_node* new_node;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_list_node_valid(node));
    MODEL_ASSERT(prop_resource_valid(r));

    /* get the parent list. */
    list* parent = node->parent;
    MODEL_ASSERT(prop_list_valid(parent));

    /* attempt to create a list_node. */
    int retval = list_node_create(&new_node, parent, r);
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

    /* set the new node's next to node's next. */
    new_node->next = node->next;

    /* set the new node's prev to node. */
    new_node->prev = node;

    /* if node next is valid, set its prev to new_node. */
    if (NULL != node->next)
    {
        node->next->prev = new_node;
    }

    /* set the new node->next. */
    node->next = new_node;

    /* increment the count. */
    ++parent->count;

    /* success. */
    return STATUS_SUCCESS;
}
