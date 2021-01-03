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

MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread);

/**
 * \brief Valid \ref thread property.
 *
 * \param th            The \ref thread instance to be verified.
 *
 * \returns true if the \ref thread instance is valid.
 */
bool prop_thread_valid(const thread* th)
{
    MODEL_ASSERT(NULL != th);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        th->MODEL_STRUCT_TAG_REF(thread), thread);

    return
        prop_resource_valid(&th->hdr);
}
