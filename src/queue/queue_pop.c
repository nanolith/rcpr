/**
 * \file queue/queue_pop.c
 *
 * \brief Pop a resource off of the front of a \ref queue.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "queue_internal.h"

/**
 * \brief Pop the head value of the \ref queue, setting the given resource
 * pointer to the resource previously held in the head node.
 *
 * The next node in the \ref queue after head becomes the new head node.
 *
 * \param q             Pointer to the \ref queue instance to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      head value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * queue node.  This queue node is released; the caller assumes ownership of the
 * \ref resource and must release it when it is no longer needed.  If the \ref
 * resource pointer is NULL, then there was either no resource associated with
 * that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p q must reference a valid \ref queue and must not be NULL.
 *
 * \post
 *      - On success, if \p queue has a at least one node, then
 *          - if the head node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the head node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the head node is released, and the next node becomes the head
 *            node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
queue_pop(
    queue* q, RCPR_SYM(resource)** r)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_queue_valid(q));
    MODEL_ASSERT(NULL != r);
    MODEL_ASSERT(NULL == *r);

    /* pop the element off of the slist. */
    return slist_pop(q->list, r);
}
