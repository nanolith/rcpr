/**
 * \file queue/queue_append.c
 *
 * \brief Append a resource to the end of a \ref queue.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "queue_internal.h"

RCPR_IMPORT_queue;

/**
 * \brief Append the given \ref resource to the back of the \ref queue.
 *
 * \param q             Pointer to the \ref queue for the append operation.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a queue node will be created to hold the
 * given \ref resource, and this node will become the tail of the \ref queue.
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
 *      - On success, \p r is appended to the tail of \p q.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(queue_append)(
    RCPR_SYM(queue)* q, RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_queue_valid(q));
    MODEL_ASSERT(prop_resource_valid(r));

    /* append this resource to the tail of our slist. */
    return slist_append_tail(q->list, r);
}
