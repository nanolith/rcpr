/**
 * \file rcpr/allocator.h
 *
 * \brief The allocator interface encapsulates the mechanism used to allocate
 * and reclaim memory.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_contracts.h>
#include <rcpr/function_decl.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/status.h>
#include <stdbool.h>
#include <stddef.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward decls */
struct RCPR_SYM(allocator);

/**
 * \brief The allocator type is a \ref resource reference to an allocator
 * instance.
 */
typedef struct RCPR_SYM(allocator) RCPR_SYM(allocator);

/**
 * \brief The allocator vtable describes the virtual methods used by an
 * allocator instance.
 */
typedef struct RCPR_SYM(allocator_vtable) RCPR_SYM(allocator_vtable);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid allocator property.
 *
 * \param alloc         The allocator instance to be verified.
 *
 * \returns true if the allocator instance is valid.
 */
bool
RCPR_SYM(prop_allocator_valid)(
    const RCPR_SYM(allocator)* alloc);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

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
RCPR_SYM(malloc_allocator_create)(
    RCPR_SYM(allocator)** alloc);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(malloc_allocator_create),
    RCPR_SYM(allocator)** alloc)
        /* the allocator pointer pointer must not be NULL. */
        RCPR_MODEL_ASSERT(NULL != alloc);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(malloc_allocator_create))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(malloc_allocator_create),
    int retval, RCPR_SYM(allocator)** alloc)
        /* on success... */
        if (STATUS_SUCCESS == retval)
        {
            /* the allocator is valid. */
            RCPR_MODEL_ASSERT(RCPR_SYM(prop_allocator_valid)(*alloc));
        }
        /* on failure... */
        else
        {
            /* the allocator pointer is set to NULL. */
            RCPR_MODEL_ASSERT(NULL == *alloc);

            /* the only error code returned is out-of-memory. */
            RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);
        }
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(malloc_allocator_create))

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
    RCPR_SYM(allocator)** alloc, void* region, size_t region_size);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

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
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(allocator_allocate),
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size)
        /* this must be a valid allocator. */
        RCPR_MODEL_ASSERT(RCPR_SYM(prop_allocator_valid(alloc)));
        /* ptr must be sized to hold the result. */
        RCPR_MODEL_CHECK_OBJECT_RW(ptr, sizeof(*ptr));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(allocator_allocate))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(allocator_allocate),
    int retval, void** ptr, size_t size)
        /* on success... */
        if (STATUS_SUCCESS == retval)
        {
            /* *ptr can hold at least size bytes. */
            RCPR_MODEL_CHECK_OBJECT_RW(*ptr, size);
        }
        /* on failure... */
        else
        {
            /* *ptr is set to NULL. */
            RCPR_MODEL_ASSERT(NULL == *ptr);
        }
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(allocator_allocate))

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
    RCPR_SYM(allocator)* alloc, void* ptr);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(allocator_reclaim),
    RCPR_SYM(allocator)* alloc, void* ptr)
        /* alloc is a valid allocator. */
        RCPR_MODEL_ASSERT(RCPR_SYM(prop_allocator_valid)(alloc));
        /* ptr is not NULL. */
        RCPR_MODEL_ASSERT(NULL != ptr);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(allocator_reclaim))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(allocator_reclaim), int retval)
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(allocator_reclaim))

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
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(allocator_reallocate),
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size)
        /* alloc is a valid allocator. */
        RCPR_MODEL_ASSERT(RCPR_SYM(prop_allocator_valid)(alloc));
        /* ptr is not NULL. */
        RCPR_MODEL_ASSERT(NULL != ptr);
        /* *ptr is not NULL. */
        RCPR_MODEL_ASSERT(NULL != *ptr);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(allocator_reallocate))

/**
 * \brief Given an allocator instance, return the resource handle for this
 * allocator instance.
 *
 * \param alloc         The allocator instance from which the resource handle is
 *                      returned.
 *
 * \returns the resource handle for this allocator instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(allocator_resource_handle)(
    RCPR_SYM(allocator)* alloc);

/******************************************************************************/
/* Start of public types.                                                     */
/******************************************************************************/

/**
 * \brief Function type for allocating memory.
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
typedef status
(*RCPR_SYM(allocator_allocate_fn))(
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size);

/**
 * \brief Function type for the allocator reclaim function.
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
typedef status
(*RCPR_SYM(allocator_reclaim_fn))(
    RCPR_SYM(allocator)* alloc, void* ptr);

/**
 * \brief Function type for the allocator reallocate function.
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
typedef status
(*RCPR_SYM(allocator_reallocate_fn))(
    RCPR_SYM(allocator)* alloc, void** ptr, size_t size);

/**
 * \brief The definition of the allocator vtable used for defining allocator
 * instances.
 */
struct RCPR_SYM(allocator_vtable)
{
    RCPR_SYM(resource_vtable) hdr;
    RCPR_SYM(allocator_allocate_fn) allocate_fn;
    RCPR_SYM(allocator_reclaim_fn) reclaim_fn;
    RCPR_SYM(allocator_reallocate_fn) reallocate_fn;
};

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_allocator_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(allocator) sym ## allocator; \
    typedef RCPR_SYM(allocator_allocate_fn) sym ## allocator_allocate_fn; \
    typedef RCPR_SYM(allocator_reclaim_fn) sym ## allocator_reclaim_fn; \
    typedef RCPR_SYM(allocator_reallocate_fn) sym ## allocator_reallocate_fn; \
    typedef RCPR_SYM(allocator_vtable) sym ## allocator_vtable; \
    static inline status FN_DECL_MUST_CHECK \
    sym ## malloc_allocator_create( \
        RCPR_SYM(allocator)** x) { \
            return RCPR_SYM(malloc_allocator_create)(x); } \
    static inline status FN_DECL_MUST_CHECK sym ## bump_allocator_create( \
        RCPR_SYM(allocator)** x, void* y, size_t z) { \
            return RCPR_SYM(bump_allocator_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## allocator_allocate( \
        RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(allocator_allocate)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## allocator_reclaim( \
        RCPR_SYM(allocator)* x, void* y) { \
            return RCPR_SYM(allocator_reclaim)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## allocator_reallocate( \
        RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(allocator_reallocate)(x,y,z); } \
    static inline RCPR_SYM(resource)* sym ## allocator_resource_handle( \
        RCPR_SYM(allocator)* x) { \
            return RCPR_SYM(allocator_resource_handle)(x); } \
    static inline bool sym ## prop_allocator_valid( \
        const RCPR_SYM(allocator)* x) { \
            return RCPR_SYM(prop_allocator_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_allocator_as(sym) \
    __INTERNAL_RCPR_IMPORT_allocator_sym(sym ## _)
#define RCPR_IMPORT_allocator \
    __INTERNAL_RCPR_IMPORT_allocator_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
