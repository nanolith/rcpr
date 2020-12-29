/**
 * \file queue/queue_count.c
 *
 * \brief Get the number of items in the queue.
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
 * \brief Given an \ref queue instance, return the count of nodes in that queue.
 *
 * \param q             The \ref queue instance for counting.
 *
 * \returns the number of nodes in the \ref queue instance.
 */
size_t queue_count(queue* q)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_queue_valid(q));

    /* return the count of this queue. */
    return q->list->count;
}
