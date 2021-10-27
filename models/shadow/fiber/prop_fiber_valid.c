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

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;
RCPR_IMPORT_stack;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber);

/**
 * \brief Valid \ref fiber property.
 *
 * \param fib           The \ref fiber instance to be verified.
 *
 * \returns true if the \ref fiber instance is valid.
 */
bool RCPR_SYM(prop_fiber_valid)(const fiber* fib)
{
    RCPR_MODEL_ASSERT(NULL != fib);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        fib->RCPR_MODEL_STRUCT_TAG_REF(fiber), fiber);

    RCPR_MODEL_ASSERT(prop_resource_valid(&fib->hdr));
    RCPR_MODEL_ASSERT(prop_allocator_valid(fib->alloc));
    if (NULL != fib->st)
    {
        RCPR_MODEL_ASSERT(prop_stack_valid(fib->st));
        RCPR_MODEL_ASSERT(NULL != fib->fn);
    }
    else
    {
        RCPR_MODEL_ASSERT(NULL == fib->fn);
        RCPR_MODEL_ASSERT(NULL == fib->context);
    }

    return true;
}
