/**
 * \file models/shadow/platform/pthread/thread/thread_mutex_struct_tag_init.c
 *
 * \brief Initialize the thread_mutex struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../../../src/platform/pthread/thread/thread_internal.h"

RCPR_IMPORT_thread;

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(thread_mutex);

void thread_mutex_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(thread_mutex);
}
