/**
 * \file rcpr/vtable.h
 *
 * \brief Helpers for vtable related mapping.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <assert.h>
#include <rcpr/function_decl.h>
#include <stdbool.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* externals provided by linker. */
extern const void* __start_rcpr_vtable;
extern const void* __stop_rcpr_vtable;

#ifdef RCPR_VTABLE_CHECK_ASSERT
# define RCPR_VTABLE_CHECK_ERROR() \
    assert("Invalid RCPR vtable pointer.")
#else
# define RCPR_VTABLE_CHECK_ERROR() \
    return ERROR_GENERAL_BAD_VTABLE
#endif /*RCPR_VTABLE_CHECK_ASSERT*/

#ifdef RCPR_VTABLE_CHECK_ASSERT
# define RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(label) \
    assert("Invalid RCPR vtable pointer.")
#else
# define RCPR_VTABLE_CHECK_ERROR_GOTO_FAIL(label) \
    retval = ERROR_GENERAL_BAD_VTABLE; \
    goto label; \
    REQUIRE_SEMICOLON_HERE
#endif /*RCPR_VTABLE_CHECK_ASSERT*/


/**
 * \brief The RCPR_VTABLE attribute macro is used when specifying that a given
 * vtable data structure should be stored in the rcpr_vtable section of the
 * binary.
 *
 * Since runtime checking of vtable pointers will be enforced in the future,
 * this attribute ensures that the given vtable is in the correct section.
 */
#if defined(__RCPR_MACOS__)
#define RCPR_VTABLE \
    static const
#else
#define RCPR_VTABLE \
    static const \
    __attribute__ ((section ("rcpr_vtable")))
#endif

/**
 * \brief The RCPR_VTABLE_CHECK macro checks to ensure that a vtable entry
 * exists in the rcpr_vtable section of memory.
 */
#ifdef RCPR_VTABLE_RUNTIME_ENFORCEMENT
#define RCPR_VTABLE_CHECK(ptr) \
    if ( \
        (ptrdiff_t)(ptr) >= (ptrdiff_t)(&__start_rcpr_vtable) \
     && (ptrdiff_t)(ptr) <= (ptrdiff_t)(&__stop_rcpr_vtable)) \
    { \
        return true; \
    } \
    return false
#else
#define RCPR_VTABLE_CHECK(ptr) \
    (void)ptr; \
    return true
#endif /*RCPR_VTABLE_RUNTIME_ENFORCEMENT*/

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_vtable_sym(sym) \
    RCPR_BEGIN_EXPORT \
    static inline bool sym ## vtable_range_valid(\
        const void* ptr) { \
            RCPR_VTABLE_CHECK(ptr); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_vtable_as(sym) \
    __INTERNAL_RCPR_IMPORT_vtable_sym(sym ## _)
#define RCPR_IMPORT_vtable \
    __INTERNAL_RCPR_IMPORT_vtable_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
