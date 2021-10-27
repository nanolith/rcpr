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

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_mutex);

/**
 * \brief Valid \ref thread property.
 *
 * \param mut           The \ref thread instance to be verified.
 *
 * \returns true if the \ref thread_mutex instance is valid.
 */
bool RCPR_SYM(prop_thread_mutex_valid)(const thread_mutex* mut)
{
    RCPR_MODEL_ASSERT(NULL != mut);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        mut->RCPR_MODEL_STRUCT_TAG_REF(thread_mutex), thread_mutex);

    return
        prop_allocator_valid(mut->alloc)
     && prop_resource_valid(&mut->hdr);
}
