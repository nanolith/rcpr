/**
 * \file rcpr/allocator.h
 *
 * \brief The allocator interface encapsulates the mechanism used to allocate
 * and reclaim memory.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
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
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_allocator_as(sym) \
    typedef RCPR_SYM(allocator) sym ## _ ## allocator; \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## malloc_allocator_create( \
        RCPR_SYM(allocator)** x) { \
            return RCPR_SYM(malloc_allocator_create)(x); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## bump_allocator_create( \
        RCPR_SYM(allocator)** x, void* y, size_t z) { \
            return RCPR_SYM(bump_allocator_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## allocator_allocate( \
        RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(allocator_allocate)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## allocator_reclaim( \
        RCPR_SYM(allocator)* x, void* y) { \
            return RCPR_SYM(allocator_reclaim)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## allocator_reallocate( \
        RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(allocator_reallocate)(x,y,z); } \
    static inline RCPR_SYM(resource)* sym ## _ ## allocator_resource_handle( \
        RCPR_SYM(allocator)* x) { \
            return RCPR_SYM(allocator_resource_handle)(x); } \
    static inline bool sym ## _ ## prop_allocator_valid( \
        const RCPR_SYM(allocator)* x) { \
            return RCPR_SYM(prop_allocator_valid)(x); } \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_allocator \
    typedef RCPR_SYM(allocator) allocator; \
    static inline status FN_DECL_MUST_CHECK malloc_allocator_create( \
        RCPR_SYM(allocator)** x) { \
            return RCPR_SYM(malloc_allocator_create)(x); } \
    static inline status FN_DECL_MUST_CHECK bump_allocator_create( \
        RCPR_SYM(allocator)** x, void* y, size_t z) { \
            return RCPR_SYM(bump_allocator_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK allocator_allocate( \
        RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(allocator_allocate)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK allocator_reclaim( \
        RCPR_SYM(allocator)* x, void* y) { \
            return RCPR_SYM(allocator_reclaim)(x,y); } \
    static inline status FN_DECL_MUST_CHECK allocator_reallocate( \
        RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(allocator_reallocate)(x,y,z); } \
    static inline RCPR_SYM(resource)* allocator_resource_handle( \
        RCPR_SYM(allocator)* x) { \
            return RCPR_SYM(allocator_resource_handle)(x); } \
    static inline bool prop_allocator_valid( \
        const RCPR_SYM(allocator)* x) { \
            return prop_allocator_valid(x); } \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
