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

RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(resource);

/**
 * \brief Valid resource property.
 *
 * \param r             The resource instance to be verified.
 *
 * \returns true if the resource instance is valid.
 */
bool RCPR_SYM(prop_resource_valid)(const RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != r);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        r->RCPR_MODEL_STRUCT_TAG_REF(resource), resource);

    return
           NULL != r
        && NULL != r->release;
}
