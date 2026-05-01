/**
 * \file allocator/bump_allocator_create.c
 *
 * \brief Create a bump allocator instance.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/vtable.h>
#include <string.h>

#include "allocator_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/* forward decls. */
static status bump_allocator_release(resource*);
static status bump_allocator_allocate(allocator*, void**, size_t);
static status bump_allocator_reclaim(allocator*, void*);
static status bump_allocator_reallocate(allocator*, void**, size_t);
static status bump_allocator_control(allocator*, int, void*, size_t);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(allocator);

/* the vtable entry for the bump allocator instance. */
RCPR_VTABLE
allocator_vtable bump_allocator_vtable = {
    .hdr = { &bump_allocator_release },
    .allocate_fn = &bump_allocator_allocate,
    .reclaim_fn = &bump_allocator_reclaim,
    .reallocate_fn = &bump_allocator_reallocate,
    .control_fn = &bump_allocator_control };

typedef struct bump_allocator bump_allocator;
struct bump_allocator
{
    RCPR_SYM(allocator) hdr;
    uint8_t* region;
    size_t offset;
    size_t max_size;
};

/**
 * \brief Create a bump allocator, backed by the given memory region.
 *
 * On success, the allocator instance is created in-place at the beginning of
 * this memory region, and the remaining space of this memory region is used for
 * subsequent allocations.
 *
 * \note This allocator is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref allocator_resource_handle on this allocator instance.
 *
 * \param alloc         Pointer to the pointer to receive the allocator on
 *                      success.
 * \param region        Pointer to a memory region to use to back this bump
 *                      allocator.
 * \param region_size   The size of this region in bytes.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition, for instance, if the memory region is too
 *        small to create an allocator instance.
 *
 * \pre \p alloc must not reference a previous allocator and must not be NULL.
 *
 * \post On success, \p alloc is set to a pointer to a valid \ref allocator
 * instance.  On failure, \p alloc is set to NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(bump_allocator_create)(
    RCPR_SYM(allocator)** alloc, void* region, size_t region_size)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(bump_allocator_create), alloc, region, region_size);

    int retval;
    bump_allocator* tmp;

    /* the region_size must be large enough to allocate the bump allocator
     * instance. */
    if (region_size < sizeof(bump_allocator))
    {
        *alloc = NULL;
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* "allocate" memory for this instance within the region. */
    tmp = (bump_allocator*)region;

    /* clear out the structure. */
    memset(tmp, 0, sizeof(bump_allocator));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->hdr.RCPR_MODEL_STRUCT_TAG_REF(allocator), allocator);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->hdr.RCPR_MODEL_STRUCT_TAG_REF(allocator), allocator);

    /* set the vtable. */
    resource_init(&tmp->hdr.hdr, &bump_allocator_vtable.hdr);
    tmp->region = region;
    tmp->offset = sizeof(bump_allocator);
    tmp->max_size = region_size;

    /* verify that the structure is now valid. */
    RCPR_MODEL_ASSERT(property_allocator_valid(&tmp->hdr));

    /* success. */
    *alloc = &tmp->hdr;
    retval = STATUS_SUCCESS;
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(bump_allocator_create), retval, alloc, region, region_size);

    return retval;
}

/**
 * \brief Release a bump allocator resource.
 *
 * \param r             Pointer to the allocator resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 */
static status bump_allocator_release(resource* r)
{
    bump_allocator* alloc = (bump_allocator*)r;

    /* clean up the bump allocator instance. */
    /* Note that since we don't own the memory region, we can't free it. */
    memset(alloc, 0, sizeof(bump_allocator));

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
static status bump_allocator_allocate(
    allocator* alloc, void** ptr, size_t size)
{
    bump_allocator* bump = (bump_allocator*)alloc;

    /* calculate a 128-bit aligned offset. */
    size_t mem_offset = bump->offset;
    size_t raw_mem_offset = (size_t)(bump->region + mem_offset);
    if (0 != raw_mem_offset % 16)
    {
        /* increment to the next 128-bit offset. */
        mem_offset += 16 - (raw_mem_offset % 16);
    }

    /* verify that this computed offset does not exceed the total size of this
     * memory region. */
    size_t bump_offset = mem_offset + size;
    if (bump_offset >= bump->max_size)
    {
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    /* bump the allocator. */
    bump->offset = bump_offset;

    /* success. */
    *ptr = (bump->region + mem_offset);
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
static status bump_allocator_reclaim(
    allocator* alloc, void* ptr)
{
    (void)alloc;
    (void)ptr;

    /* The bump allocator cannot reclaim memory, so just succeed. */
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
static status bump_allocator_reallocate(
    allocator* alloc, void** ptr, size_t size)
{
    (void)alloc;
    (void)ptr;
    (void)size;

    /* bump allocator does not support reallocation. */
    return ERROR_GENERAL_REALLOCATION_NOT_SUPPORTED;
}

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
static status bump_allocator_control(
    allocator* alloc, int key, void* value, size_t value_size)
{
    (void)value;
    (void)value_size;
    bump_allocator* bump = (bump_allocator*)alloc;

    switch (key)
    {
        case RCPR_ALLOCATOR_CONTROL_BUMP_ALLOCATOR_RESET:
            bump->offset = sizeof(bump_allocator);
            return STATUS_SUCCESS;

        default:
            return ERROR_GENERAL_CONTROL_KEY_INVALID;
    }
}
