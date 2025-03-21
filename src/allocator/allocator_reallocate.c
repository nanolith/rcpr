/**
 * \file allocator/allocator_reallocate.c
 *
 * \brief Reallocate memory using the given allocator.
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
 * \brief Attempt to resize a previously allocated memory region, either growing
 * or shrinking it.
 *
 * On success, \ref ptr is updated to a new memory region of the given size.  If
 * this method fails, then \ref ptr is unchanged and must be reclaimed when no
 * longer needed.  If this method succeeds, then the updated \ref ptr should be
 * reclaimed, and the previous \ref ptr value should not be used by the caller.
 *
 * \param alloc         The allocator instance to use to resize this memory
 *                      region.
 * \param ptr           Pointer to the pointer set to the current region which
 *                      the caller wishes to resize.
 * \param size          The new size of the region.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *      - ERROR_GENERAL_UNSUPPORTED_OPERATION if this operation is unsupported
 *        by this allocator instance.
 *
 * \pre \p alloc must be a valid \ref allocator instance. \p ptr must not be
 * NULL and must point to a memory region previously allocated or reallocated by
 * this \ref allocator instance.
 *
 * \post On success, \p ptr is set to a pointer to a memory region that is
 * \p size bytes in size.  On failure, \p ptr is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(allocator_reallocate)(
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(allocator_reallocate), alloc, ptr, size);

    int retval;

    const allocator_vtable* vtable = allocator_vtable_get(alloc);

    /* vtable runtime check. */
    if (!vtable_range_valid(vtable))
    {
        RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(done);
    }

    retval = vtable->reallocate_fn(alloc, ptr, size);
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(allocator_reallocate), retval, ptr, size);

    return retval;
}
