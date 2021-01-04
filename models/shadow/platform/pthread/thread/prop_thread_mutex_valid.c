/**
 * \file models/shadow/platform/pthread/thread/prop_thread_mutex_valid.c
 *
 * \brief Check whether a thread_mutex instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../../../src/platform/pthread/thread/thread_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_mutex);

/**
 * \brief Valid \ref thread property.
 *
 * \param mut           The \ref thread instance to be verified.
 *
 * \returns true if the \ref thread_mutex instance is valid.
 */
bool prop_thread_mutex_valid(const thread_mutex* mut)
{
    MODEL_ASSERT(NULL != mut);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        mut->MODEL_STRUCT_TAG_REF(thread_mutex), thread_mutex);

    return
        prop_allocator_valid(mut->alloc)
     && prop_resource_valid(&mut->hdr);
}
