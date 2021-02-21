/**
 * \file models/shadow/fiber/prop_fiber_valid.c
 *
 * \brief Check whether a fiber instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/fiber/common/fiber_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber);

/**
 * \brief Valid \ref fiber property.
 *
 * \param fib           The \ref fiber instance to be verified.
 *
 * \returns true if the \ref fiber instance is valid.
 */
bool prop_fiber_valid(const fiber* fib)
{
    MODEL_ASSERT(NULL != fib);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        fib->MODEL_STRUCT_TAG_REF(fiber), fiber);

    return
        prop_resource_valid(&fib->hdr)
     && prop_allocator_valid(fib->alloc)
     && (       (NULL != fib->st
              && prop_stack_valid(fib->st)
              && NULL != fib->fn)
         ||     (NULL == fib->st
              && NULL == fib->fn
              && NULL == fib->context));
}
