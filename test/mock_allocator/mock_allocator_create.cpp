/**
 * \file test/mock_allocator/mock_allocator_create.c
 *
 * \brief Create a mock allocator instance.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <string.h>

#include "../../src/allocator/allocator_internal.h"
#include "mock_allocator.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_mock_allocator;
RCPR_IMPORT_resource;

/* forward decls. */
static status mock_allocator_context_release(resource*);
static status mock_allocator_release(resource*);
static status mock_allocator_allocate(allocator*, void**, size_t);
static status mock_allocator_reclaim(allocator*, void*);
static status mock_allocator_reallocate(allocator*, void**, size_t);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(allocator);

/**
 * \brief Create a mock allocator.
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
RCPR_SYM(mock_allocator_create)(
    RCPR_SYM(allocator)** alloc)
{
    status retval, release_retval;
    allocator* backing = NULL;
    allocator* tmp = NULL;
    mock_allocator_context* ctx = NULL;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != alloc);

    /* create the malloc allocator that we use to back this allocator. */
    retval = malloc_allocator_create(&backing);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* attempt to allocate memory for the mock context. */
    retval = allocator_allocate(backing, (void**)&ctx, sizeof(*ctx));
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_backing;
    }

    /* clear out the structure. */
    memset(ctx, 0, sizeof(*ctx));

    /* initialize the resource. */
    resource_init(&ctx->hdr, &mock_allocator_context_release);
    ctx->backing_allocator = backing;

    /* attempt to allocate memory for the mock allocator. */
    retval = allocator_allocate(backing, (void**)&tmp, sizeof(*tmp));
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_ctx;
    }

    /* clear out the structure. */
    memset(tmp, 0, sizeof(*tmp));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(allocator), allocator);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(allocator), allocator);

    /* set the release method. */
    resource_init(&tmp->hdr, &mock_allocator_release);

    /* set the callbacks. */
    tmp->allocate_fn = &mock_allocator_allocate;
    tmp->reclaim_fn = &mock_allocator_reclaim;
    tmp->reallocate_fn = &mock_allocator_reallocate;

    /* set the context. */
    tmp->context = (void*)ctx;

    /* verify that the structure is now valid. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(tmp));

    /* success. */
    retval = STATUS_SUCCESS;
    *alloc = tmp;
    goto done;

cleanup_ctx:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_backing:
    release_retval = resource_release(allocator_resource_handle(backing));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release a mock allocator context resource.
 *
 * \param r             Pointer to the mock allocator context resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 */
static status mock_allocator_context_release(resource* r)
{
    status reclaim_retval = STATUS_SUCCESS;
    status allocator_release_retval = STATUS_SUCCESS;
    mock_allocator_context* ctx = (mock_allocator_context*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_resource_valid(r));
    RCPR_MODEL_ASSERT(prop_mock_allocator_context_valid(ctx));

    /* cache allocator. */
    allocator* alloc = ctx->backing_allocator;

    /* clean up the context. */
    memset(ctx, 0, sizeof(*ctx));
    reclaim_retval = allocator_reclaim(alloc, ctx);

    /* clean up the backing allocator. */
    allocator_release_retval =
        resource_release(allocator_resource_handle(alloc));

    /* Decode return value. */
    if (STATUS_SUCCESS != allocator_release_retval)
    {
        return allocator_release_retval;
    }
    else
    {
        return reclaim_retval;
    }
}

/**
 * \brief Release a mock allocator resource.
 *
 * \param r             Pointer to the mock allocator resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 */
static status mock_allocator_release(resource* r)
{
    status reclaim_retval = STATUS_SUCCESS;
    status context_release_retval = STATUS_SUCCESS;
    allocator* a = (allocator*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_resource_valid(r));
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));

    /* get the context. */
    mock_allocator_context* ctx = (mock_allocator_context*)a->context;
    RCPR_MODEL_ASSERT(prop_mock_allocator_context_valid(ctx));

    /* cache allocator. */
    allocator* alloc = ctx->backing_allocator;

    /* clean up the mock allocator. */
    memset(a, 0, sizeof(*a));
    reclaim_retval = allocator_reclaim(alloc, a);

    /* clean up the context. */
    context_release_retval = resource_release(&ctx->hdr);

    /* Decode return value. */
    if (STATUS_SUCCESS != context_release_retval)
    {
        return context_release_retval;
    }
    else
    {
        return reclaim_retval;
    }
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
static status mock_allocator_allocate(
    allocator* alloc, void** ptr, size_t size)
{
    mock_allocator_context* ctx = (mock_allocator_context*)alloc->context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_mock_allocator_context_valid(ctx));
    RCPR_MODEL_ASSERT(NULL != ptr);

    /* should we fail? */
    if (STATUS_SUCCESS != ctx->allocate_status)
    {
        return ctx->allocate_status;
    }

    /* fall back to the backing allocator. */
    return allocator_allocate(ctx->backing_allocator, ptr, size);
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
static status mock_allocator_reclaim(
    allocator* alloc, void* ptr)
{
    mock_allocator_context* ctx = (mock_allocator_context*)alloc->context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_mock_allocator_context_valid(ctx));
    RCPR_MODEL_ASSERT(NULL != ptr);

    /* fall back to the backing allocator. */
    return allocator_reclaim(ctx->backing_allocator, ptr);
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
static status mock_allocator_reallocate(
    allocator* alloc, void** ptr, size_t size)
{
    mock_allocator_context* ctx = (mock_allocator_context*)alloc->context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_mock_allocator_context_valid(ctx));
    RCPR_MODEL_ASSERT(NULL != ptr);

    /* should we fail? */
    if (STATUS_SUCCESS != ctx->allocate_status)
    {
        return ctx->allocate_status;
    }

    /* fall back to the backing allocator. */
    return allocator_reallocate(ctx->backing_allocator, ptr, size);
}
