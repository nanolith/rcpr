/**
 * \file allocator/allocator_allocate.c
 *
 * \brief Allocate memory using the given allocator.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "allocator_internal.h"

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
allocator_allocate(allocator* alloc, void** ptr, size_t size)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(NULL != ptr);

    return
        alloc->allocate_fn(alloc, ptr, size);
}
