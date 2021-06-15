/**
 * \file list/list_append_tail.c
 *
 * \brief Append a resource to the tail of an \ref list.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

/**
 * \brief Append the given \ref resource to the back of the \ref list.
 *
 * \param l             Pointer to the \ref list for the append operation.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the tail of the list.  The
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
 *      - On success, \p r is appended to the end of \p l.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
list_append_tail(
    list* l, RCPR_SYM(resource)* r)
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

    /* do we have nodes in our list? */
    if (NULL != l->tail)
    {
        node->prev = l->tail;
        l->tail->next = node;
        l->tail = node;
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
