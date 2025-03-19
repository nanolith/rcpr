/**
 * \file allocator/allocator_allocate.c
 *
 * \brief Allocate memory using the given allocator.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/vtable.h>

#include "allocator_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_allocator_internal;
RCPR_IMPORT_vtable;

/**
 * \brief Allocate memory using the given allocator instance.
 *
 * On success, \ref ptr is set to a pointer that is \ref size bytes in size.
 * When this memory is no longer needed, \ref allocator_reclaim() should be
 * called on this region so that this allocator instance can reclaim it.
 *
 * \param alloc         The allocator instance from which this memory is
 *                      allocated.
 * \param ptr           Pointer to the pointer to receive the memory.
 * \param size          The size of the memory region, in bytes, to allocate.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre \p alloc must be a valid \ref allocator instance and \p ptr must not be
 * NULL.
 *
 * \post On success, \p ptr is set to a pointer to a memory region that is
 * \p size bytes in size.  On failure, \p ptr is set to NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(allocator_allocate)(
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(allocator_allocate), alloc, ptr, size);

    int retval;

    /* get the allocator vtable. */
    const allocator_vtable* vtable = allocator_vtable_get(alloc);

    /* vtable runtime check. */
    if (!vtable_range_valid(vtable))
    {
        *ptr = NULL;
        RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(done);
    }

    retval = vtable->allocate_fn(alloc, ptr, size);
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(allocator_allocate), retval, ptr, size);

    return retval;
}
