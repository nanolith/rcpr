/**
 * \file resource/resource_init.c
 *
 * \brief Initialize a resource with a release method.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "resource_internal.h"

RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(resource);

/**
 * \brief Initialize a resource with the given resource vtable.
 *
 * \param r         The resource to be initialized.
 * \param vtable    The resource vtable to use for this resource.
 */
void
RCPR_SYM(resource_init)(
    RCPR_SYM(resource)* r, const RCPR_SYM(resource_vtable)* vtable)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(resource_init), r, vtable);

    r->vtable = vtable;

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        r->RCPR_MODEL_STRUCT_TAG_REF(resource), resource);

    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(resource_init), r);
}
