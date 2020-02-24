/**
 * \file models/shadow/resource/prop_resource_valid.c
 *
 * \brief Check whether a resource instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/resource/resource_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(resource);

/**
 * \brief Valid resource property.
 *
 * \param r             The resource instance to be verified.
 *
 * \returns true if the resource instance is valid.
 */
bool prop_resource_valid(const resource* r)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != r);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        r->MODEL_STRUCT_TAG_REF(resource), resource);

    return
           NULL != r
        && NULL != r->release;
}
