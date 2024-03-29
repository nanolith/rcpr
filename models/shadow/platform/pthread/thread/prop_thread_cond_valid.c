/**
 * \file models/shadow/platform/pthread/thread/prop_thread_cond_valid.c
 *
 * \brief Check whether a thread_cond instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../../../src/platform/pthread/thread/thread_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_cond);

/**
 * \brief Valid \ref thread property.
 *
 * \param cond          The \ref thread instance to be verified.
 *
 * \returns true if the \ref thread_cond instance is valid.
 */
bool RCPR_SYM(prop_thread_cond_valid)(const RCPR_SYM(thread_cond)* cond)
{
    RCPR_MODEL_ASSERT(NULL != cond);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        cond->RCPR_MODEL_STRUCT_TAG_REF(thread_cond), thread_cond);

    return
        prop_allocator_valid(cond->alloc)
     && prop_resource_valid(&cond->hdr);
}
