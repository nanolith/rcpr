/**
 * \file models/shadow/stack/prop_stack_valid.c
 *
 * \brief Check whether a stack instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/stack/stack_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_stack;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(stack);

/**
 * \brief Valid \ref stack property.
 *
 * \param st             The \ref stack instance to be verified.
 *
 * \returns true if the \ref stack instance is valid.
 */
bool RCPR_SYM(prop_stack_valid)(const stack* st)
{
    RCPR_MODEL_ASSERT(NULL != st);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        st->RCPR_MODEL_STRUCT_TAG_REF(stack), stack);

    return
        prop_resource_valid(&st->hdr)
     && prop_allocator_valid(st->alloc)
     && (st->region != NULL && st->size > 0);
}
