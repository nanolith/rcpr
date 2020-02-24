/**
 * \file allocator/malloc_allocator_create.c
 *
 * \brief Create a malloc allocator instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>

#include "allocator_internal.h"

/* forward decls. */
static status malloc_allocator_release(resource*);
static status malloc_allocator_allocate(allocator*, void**, size_t);
static status malloc_allocator_reclaim(allocator*, void*);
static status malloc_allocator_reallocate(allocator*, void**, size_t);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(allocator);

/**
 * \brief Create an allocator backed by malloc / free.
 *
 * \param alloc         Pointer to the pointer to receive the allocator on
 *                      success.
 *
 * \note This allocator is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref allocator_resource_handle on this allocator instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre \p alloc must not reference a previous allocator and must not be NULL.
 *
 * \post On success, \p alloc is set to a pointer to a valid \ref allocator
 * instance.  On failure, \p alloc is set to NULL.
 */
status FN_DECL_MUST_CHECK
malloc_allocator_create(allocator** alloc)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != alloc);

    /* attempt to allocate memory for the allocator. */
    *alloc = (allocator*)malloc(sizeof(allocator));
    if (NULL == *alloc)
    {
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    /* clear out the structure. */
    memset(*alloc, 0, sizeof(allocator));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        (*alloc)->MODEL_STRUCT_TAG_REF(allocator), allocator);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT((*alloc)->MODEL_STRUCT_TAG_REF(allocator), allocator);

    /* set the release method. */
    (*alloc)->hdr.release = &malloc_allocator_release;

    /* set the callbacks. */
    (*alloc)->allocate_fn = &malloc_allocator_allocate;
    (*alloc)->reclaim_fn = &malloc_allocator_reclaim;
    (*alloc)->reallocate_fn = &malloc_allocator_reallocate;

    /* verify that the structure is now valid. */
    MODEL_ASSERT(prop_allocator_valid(*alloc));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Release an allocator resource.
 *
 * \param r             Pointer to the allocator resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 */
static status malloc_allocator_release(resource* r)
{
    allocator* alloc = (allocator*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_resource_valid(r));
    MODEL_ASSERT(prop_allocator_valid(alloc));

    /* clean up the malloc allocator instance. */
    memset(alloc, 0, sizeof(allocator));
    free(alloc);

    /* success. */
    return STATUS_SUCCESS;
}

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
static status malloc_allocator_allocate(
    allocator* alloc, void** ptr, size_t size)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(NULL != ptr);

    /* attempt to allocate memory. */
    *ptr = malloc(size);
    if (NULL == *ptr)
    {
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    /* success. */
    return STATUS_SUCCESS;
}

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
static status malloc_allocator_reclaim(
    allocator* alloc, void* ptr)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(NULL != ptr);

    /* release the memory allocated by malloc. */
    free(ptr);

    /* success. */
    return STATUS_SUCCESS;
}

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
static status malloc_allocator_reallocate(
    allocator* alloc, void** ptr, size_t size)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(NULL != ptr);

    /* attempt to reallocate memory. */
    void* newptr = realloc(*ptr, size);
    if (NULL == newptr)
    {
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    /* success. */
    *ptr = newptr;
    return STATUS_SUCCESS;
}
