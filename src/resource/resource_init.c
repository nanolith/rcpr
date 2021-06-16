/**
 * \file resource/resource_init.c
 *
 * \brief Initialize a resource with a release method.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "resource_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(resource);

/**
 * \brief Initialize a resource with the given release method.
 *
 * \param r         The resource to be initialized.
 * \param release   The release method to use to release this resource.
 */
void
RCPR_SYM(resource_init)(
    RCPR_SYM(resource)* r, RCPR_SYM(resource_release_fn) release)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != r);
    MODEL_ASSERT(NULL != release);

    r->release = release;

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(r->MODEL_STRUCT_TAG_REF(resource), resource);

    /* verify that the resource is now valid. */
    MODEL_ASSERT(prop_resource_valid(r));
}
