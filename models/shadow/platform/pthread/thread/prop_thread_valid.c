/**
 * \file models/shadow/platform/pthread/thread/prop_thread_valid.c
 *
 * \brief Check whether a thread instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../../../src/platform/pthread/thread/thread_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread);

/**
 * \brief Valid \ref thread property.
 *
 * \param th            The \ref thread instance to be verified.
 *
 * \returns true if the \ref thread instance is valid.
 */
bool RCPR_SYM(prop_thread_valid)(const thread* th)
{
    RCPR_MODEL_ASSERT(NULL != th);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        th->RCPR_MODEL_STRUCT_TAG_REF(thread), thread);

    return
        prop_allocator_valid(th->alloc)
     && prop_resource_valid(&th->hdr);
}
