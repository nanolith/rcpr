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

RCPR_IMPORT_resource;
RCPR_IMPORT_slist;
RCPR_IMPORT_slist_internal;

/**
 * \brief Append the given \ref resource to the back of the \ref slist.
 *
 * \param list          Pointer to the \ref slist for the append operation.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref slist_node will be created to hold the
 * given \ref resource, and this node will become the tail of the list.  The
 * \ref slist takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p list must be a valid \ref slist instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended to the end of \p list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_append_tail)(
    RCPR_SYM(slist)* list, RCPR_SYM(resource)* r)
{
    slist_node* node;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_slist_valid(list));
    RCPR_MODEL_ASSERT(prop_resource_valid(r));

    /* attempt to create an slist_node. */
    int retval = slist_node_create(&node, list, r);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* do we have nodes in our list? */
    if (NULL != list->tail)
    {
        list->tail->next = node;
        list->tail = node;
    }
    else
    {
        list->head = node;
        list->tail = node;
    }

    /* increment count. */
    ++list->count;

    /* success. */
    return STATUS_SUCCESS;
}
