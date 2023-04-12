/**
 * \file rcpr/test/mock_allocator.h
 *
 * \brief Mock allocator interface.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

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
    RCPR_SYM(allocator)** alloc);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Change the return status for an allocate / reallocate call.
 *
 * If the return status is a failing (non-zero / STATUS_SUCCESS) status, then
 * this status is returned instead of performing the wrapped operation. However,
 * if the return status is zero / STATUS_SUCCESS, then the wrapped malloc
 * allocator is called instead, and its return status is returned to the caller.
 * This allows the caller to simulate error conditions during memory allocation.
 *
 * \param alloc         The mock allocator instance to modify.
 * \param status_code   The status code to return on allocate / reallocate.
 *
 * \pre \p alloc must be a valid \ref allocator instance created as a mock
 * allocator.
 *
 * \post On success, the return status for \p alloc is modified for allocate and
 * reallocate operations.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(mock_allocator_allocate_status_code_set)(
    RCPR_SYM(allocator)* alloc, status status_code);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_mock_allocator_sym(sym) \
    RCPR_BEGIN_EXPORT \
    static inline status FN_DECL_MUST_CHECK \
    sym ## mock_allocator_create( \
        RCPR_SYM(allocator)** x) { \
            return RCPR_SYM(malloc_allocator_create)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_mock_allocator_as(sym) \
    __INTERNAL_RCPR_IMPORT_mock_allocator_sym(sym ## _)
#define RCPR_IMPORT_mock_allocator \
    __INTERNAL_RCPR_IMPORT_mock_allocator_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
