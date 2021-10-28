/**
 * \file models/shadow/queue/queue_struct_tag_init.c
 *
 * \brief Initialize the queue struct tag.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/queue/queue_internal.h"

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(queue);

void queue_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(queue);
}
