/**
 * \file list/list_pop.c
 *
 * \brief Pop the head value of the list.
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
 * \brief Pop the head value of the list, setting the given resource pointer to
 * the resource previously held in the head node.
 *
 * The next node in the list after head becomes the new head node.
 *
 * \param l             Pointer to the \ref list instance to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      head value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * \ref list_node.  This \ref list_node is released; the caller assumes
 * ownership of the \ref resource and must release it when it is no longer
 * needed.  If the \ref resource pointer is NULL, then there was either no
 * resource associated with that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p l must reference a valid \ref list and must not be NULL.
 *
 * \post
 *      - On success, if \p l has a at least one node, then
 *          - if the head node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the head node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the head node is released, and the next node becomes the head
 *            node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
list_pop(
    list* l, resource** r)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_list_valid(l));
    MODEL_ASSERT(NULL != r);
    MODEL_ASSERT(NULL == *r);

    /* does the head node exist? */
    if (NULL != l->head)
    {
        /* is it the same as the tail? */
        if (l->head == l->tail)
        {
            /* the tail will be NULL when we're done. */
            l->tail = NULL;
        }

        /* save the head node as tmp. */
        list_node* tmp = l->head;

        /* save the resource from the head node. */
        *r = tmp->child;

        /* the caller now owns this resource. */
        tmp->child = NULL;

        /* set head to the next node, if it exists. */
        l->head = tmp->next;

        /* if the next node exists, set its prev to NULL. */
        if (l->head)
        {
            l->head->prev = NULL;
        }

        /* we are releasing this node, so its parent and next must be NULL. */
        tmp->parent = NULL;
        tmp->next = NULL;

        /* reduce the count by 1. */
        --l->count;

        /* get the resource handle for this node. */
        resource* tmp_handle = list_node_resource_handle(tmp);

        /* attempt to release this node. */
        status retval = resource_release(tmp_handle);
        if (STATUS_SUCCESS != retval)
        {
            /* save the cleanup resource value. */
            resource* cleanup_resource = *r;

            /* on failure, *r is set to NULL. */
            *r = NULL;

            /* clean up the resource, if possible. */
            retval = resource_release(cleanup_resource);
            if (STATUS_SUCCESS != retval)
            {
                /* bubble up the error for the resource release first. */
                return retval;
            }

            /* return the status to the caller. */
            return retval;
        }

        /* success. */
        return STATUS_SUCCESS;
    }
    else
    {
        /* change nothing. */
        return STATUS_SUCCESS;
    }
}
