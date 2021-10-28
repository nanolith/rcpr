/**
 * \file queue/queue_insert.c
 *
 * \brief Insert a resource to the head of a \ref queue.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "queue_internal.h"

RCPR_IMPORT_queue;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

/**
 * \brief Place the given \ref resource at the front of the \ref queue.
 *
 * \param q             Pointer to the \ref queue for the insert operation.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a queue node will be created to hold the
 * given \ref resource, and this node will become the head of the \ref queue.
 * The \ref queue takes ownership of the \ref resource pointed to by \p r and
 * will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p q must be a valid \ref queue instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted to the head of \p q.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(queue_insert)(
    RCPR_SYM(queue)* q, RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_queue_valid(q));
    RCPR_MODEL_ASSERT(prop_resource_valid(r));

    /* insert this resource to the head of our slist. */
    return slist_insert_head(q->list, r);
}
