/**
 * \file allocator/allocator_reclaim.c
 *
 * \brief Reclaim memory using the given allocator.
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
 * \brief Instruct the allocator instance to reclaim the given memory region.
 *
 * On success, the allocator instance reclaims the given memory region.  After
 * calling this method, user code cannot access this memory region or any subset
 * of this memory region.  The \ref ptr parameter MUST be a region pointer
 * originally assigned by this allocator instance.
 *
 * \param alloc         The allocator instance to reclaim this memory region.
 * \param ptr           Pointer to the memory region to reclaim.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre \p alloc must be a valid \ref allocator instance.  \p ptr must not be
 * NULL and must point to a memory region previously allocated by this \ref
 * allocator instance.
 *
 * \post the memory region referenced by \p ptr is reclaimed and must not be
 * used by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(allocator_reclaim)(
    RCPR_SYM(allocator)* alloc, void* ptr)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(allocator_reclaim), alloc, ptr);

    int retval;

    /* get the allocator vtable. */
    const allocator_vtable* vtable = allocator_vtable_get(alloc);

    /* vtable runtime check. */
    if (!vtable_range_valid(vtable))
    {
        RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(done);
    }

    retval = vtable->reclaim_fn(alloc, ptr);
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(allocator_reclaim), alloc);

    return retval;
}
