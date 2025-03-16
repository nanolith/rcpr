/**
 * \file models/shadow/bigint/prop_bigint_valid.c
 *
 * \brief Check whether a bigint instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/bigint/bigint_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_bigint;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(bigint);

/**
 * \brief Valid \ref bigint property.
 *
 * \param i              The \ref bigint instance to be verified.
 *
 * \returns true if the \ref bigint instance is valid.
 */
bool RCPR_SYM(prop_bigint_valid)(const bigint* i)
{
    RCPR_MODEL_ASSERT(NULL != i);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        i->RCPR_MODEL_STRUCT_TAG_REF(bigint), bigint);
    RCPR_MODEL_ASSERT(i->length > 0);
    RCPR_MODEL_ASSERT(NULL != i->array);
    RCPR_MODEL_ASSERT(i->array[0] == i->array[0]);
    RCPR_MODEL_ASSERT(i->array[i->length - 1] == i->array[i->length - 1]);

    return
        prop_resource_valid(&i->hdr)
     && prop_allocator_valid(i->a)
     && i->length > 0;
}
