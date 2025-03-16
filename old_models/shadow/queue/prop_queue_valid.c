/**
 * \file models/shadow/queue/prop_queue_valid.c
 *
 * \brief Check whether a queue instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/queue/queue_internal.h"

RCPR_IMPORT_queue;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(queue);

/**
 * \brief Valid \ref queue property.
 *
 * \param q               The \ref queue instance to be verified.
 *
 * \returns true if the \ref queue instance is valid.
 */
bool RCPR_SYM(prop_queue_valid)(const queue* q)
{
    RCPR_MODEL_ASSERT(NULL != q);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        q->RCPR_MODEL_STRUCT_TAG_REF(queue), queue);

    return
        prop_resource_valid(&q->hdr)
     && prop_slist_valid(q->list);
}
