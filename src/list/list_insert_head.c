/**
 * \file list/list_insert_head.c
 *
 * \brief Insert a resource into the head of an \ref list.
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
RCPR_IMPORT_list_internal;

/**
 * \brief Insert the given \ref resource in the front of the \ref list.
 *
 * \param l             Pointer to the \ref list for the insert operation.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the head of the list.  The
 * \ref list takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p l must be a valid \ref list instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted to the head of \p l.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_insert_head)(
    RCPR_SYM(list)* l, RCPR_SYM(resource)* r)
{
    list_node* node;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_list_valid(l));
    MODEL_ASSERT(prop_resource_valid(r));

    /* attempt to create an list_node. */
    int retval = list_node_create(&node, l, r);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* save head to this node's next. */
    node->next = l->head;

    /* this node is going to be head, so it has no prev. */
    node->prev = NULL;

    /* do we have nodes in our l? */
    if (NULL != l->head)
    {
        l->head = node;

        /* set the previous head's prev to this node. */
        node->next->prev = node;
    }
    else
    {
        l->head = node;
        l->tail = node;
    }

    /* increment count. */
    ++l->count;

    /* success. */
    return STATUS_SUCCESS;
}
