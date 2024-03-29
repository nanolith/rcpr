/**
 * \file queue/queue_resource_handle.c
 *
 * \brief Get the resource handle for this queue.
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
 * \brief Given an \ref queue instance, return the resource handle for this
 * \ref queue instance.
 *
 * \param q             The \ref queue instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref queue instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(queue_resource_handle)(
    RCPR_SYM(queue)* q)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_queue_valid(q));

    /* return the resource handle for this queue. */
    return &q->hdr;
}
