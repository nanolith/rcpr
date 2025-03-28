/**
 * \file resource/resource_vtable_read.c
 *
 * \brief Read the vtable for a resource.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>

#include "resource_internal.h"

RCPR_IMPORT_resource;
RCPR_IMPORT_vtable;

/**
 * \brief Access the vtable associated with this resource.
 *
 * \param vtable    Pointer to the vtable pointer to set on success.
 * \param r         The resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_BAD_VTABLE if the vtable for this instance is invalid.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(resource_vtable_read)(
    const RCPR_SYM(resource_vtable)** vtable, const RCPR_SYM(resource)* r)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(resource_vtable_read), vtable, r);

    int retval;

    /* vtable runtime check. */
    if (!vtable_range_valid(r->vtable))
    {
        RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(done);
    }

    /* set the vtable value. */
    *vtable = r->vtable;

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(resource_vtable_read), retval, vtable);

    return retval;
}
