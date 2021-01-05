/**
 * \file
 * models/shadow/platform/pthread/thread/thread_mutex_lock_struct_tag_init.c
 *
 * \brief Initialize the thread_mutex_lock struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../../../src/platform/pthread/thread/thread_internal.h"

int MODEL_STRUCT_TAG_GLOBAL_REF(thread_mutex_lock);

void thread_mutex_lock_struct_tag_init()
{
    MODEL_STRUCT_TAG_GLOBAL_INIT(thread_mutex_lock);
}
