/**
 * \file slist/slist_node_next_pop.c
 *
 * \brief Pop the next value of the given node.
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
 * \brief Pop the next value of the given node, setting the given resource
 * pointer to the resource previously held by the next node.
 *
 * The next node in the list after node next becomes node next.
 *
 * \param node          Pointer to the \ref slist_node instance prior to the
 *                      node to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      next node value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * \ref slist_node.  This \ref slist_node is released; the caller assumes
 * ownership of the \ref resource and must release it when it is no longer
 * needed.  If the \ref resource pointer is NULL, then there was either no
 * resource associated with that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p node must reference a valid \ref slist_node and must not be NULL.
 *
 * \post
 *      - On success, if \p node has a at least one next node, then
 *          - if the next node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the next node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the next node is released, and the next next node becomes the next
 *            node for \p node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_next_pop)(
    RCPR_SYM(slist_node)* node, RCPR_SYM(resource)** r)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_slist_node_valid(node));
    MODEL_ASSERT(NULL != r);
    MODEL_ASSERT(NULL == *r);

    /* get the parent slist for this node. */
    slist* parent = node->parent;

    /* does the next node exist? */
    if (NULL != node->next)
    {
        /* is it the same as the tail? */
        if (node->next == parent->tail)
        {
            /* the tail will become node as part of this. */
            parent->tail = node;
        }

        /* save the next node as tmp. */
        slist_node* tmp = node->next;

        /* save the resource from the next node. */
        *r = tmp->child;

        /* the caller now owns this resource. */
        tmp->child = NULL;

        /* set the node next to tmp next. */
        node->next = tmp->next;

        /* we are releasing this node, so its parent and next must be NULL. */
        tmp->parent = NULL;
        tmp->next = NULL;

        /* reduce parent's count by 1. */
        --parent->count;

        /* get the resource handle for this node. */
        resource* tmp_handle = slist_node_resource_handle(tmp);

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
