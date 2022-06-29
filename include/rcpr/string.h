/**
 * \file rcpr/string.h
 *
 * \brief Basic string operations in RCPR.
 *
 * This string library unifies some basic string operations in ANSI C with the
 * RCPR allocator. It also provides some helper functions that don't exist in
 * ANSI C, such as \ref strcatv.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Duplicate a string, creating a duplicate backed by the given allocator
 * instance.
 *
 * On success, the string is duplicated, and the output string pointer is
 * updated with the duplicate string. This string is owned by the caller, and
 * when it is no longer needed, it must be reclaimed using the same allocator
 * used to in this operation.
 *
 * \param output        Pointer to receive the duplicated string on success.
 * \param alloc         The allocator instance to use for this operation.
 * \param input         Pointer to the string to be duplicated in this
 *                      operation.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(strdup)(
    char** output, RCPR_SYM(allocator)* alloc, const char* input);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_string_sym(sym) \
    RCPR_BEGIN_EXPORT \
    static inline status FN_DECL_MUST_CHECK \
    sym ## strdup( \
        char** x, RCPR_SYM(allocator)* y, const char* z) { \
            return RCPR_SYM(strdup)(x,y,z); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_string_as(sym) \
    __INTERNAL_RCPR_IMPORT_string_sym(sym ## _)
#define RCPR_IMPORT_string \
    __INTERNAL_RCPR_IMPORT_string_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
