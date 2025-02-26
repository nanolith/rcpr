/**
 * \file resource/resource_vtable_get.c
 *
 * \brief Get the vtable for a resource.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "resource_internal.h"

RCPR_IMPORT_resource;

/**
 * \brief Get the vtable associated with a resource.
 *
 * \param r         The resource.
 *
 * \returns the vtable associated with this resource.
 */
const RCPR_SYM(resource_vtable)*
RCPR_SYM(resource_vtable_get)(RCPR_SYM(resource)* r)
{
    RCPR_MODEL_ASSERT(prop_resource_valid(r));

    return r->vtable;
}
