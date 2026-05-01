/**
 * \file allocator/allocator_control.c
 *
 * \brief Adjust a control for an allocator instance.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/vtable.h>

#include "allocator_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_allocator_internal;
RCPR_IMPORT_vtable;

/**
 * \brief Adjust a control for the given allocator.
 *
 * On success, The control setting is updated.
 *
 * \param alloc         The allocator instance for this control operation.
 * \param key           The control key to set.
 * \param value         The control value to set.
 * \param value_size    The size of this value in bytes.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_CONTROL_KEY_INVALID if the control key is invalid for
 *        this allocator type.
 *
 * \pre \p alloc must be a valid \ref allocator instance. \p key must be an
 * allocator control key as defined in the allocator header. \p value and
 * \p value_size must be appropriate for this control feature.
 *
 * \post On success, \p alloc is updated based on the control setting.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(allocator_control)(
    RCPR_SYM(allocator)* alloc, int key, void* value, size_t value_size)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(allocator_control), alloc, key, value, value_size);

    int retval;

    /* get the allocator vtable. */
    const allocator_vtable* vtable = allocator_vtable_get(alloc);

    /* vtable runtime check. */
    if (!vtable_range_valid(vtable))
    {
        RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(done);
    }

    /* is the control function set? */
    if (NULL == vtable->control_fn)
    {
        retval = ERROR_GENERAL_CONTROL_KEY_INVALID;
        goto done;
    }

    retval = vtable->control_fn(alloc, key, value, value_size);
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(allocator_control), retval, alloc, key, value, value_size);

    return retval;
}
