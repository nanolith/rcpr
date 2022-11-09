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
#include <stdarg.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Return true if the given character is a whitespace character.
 *
 * \brief ch            The character to test.
 *
 * \returns true if the character is a whitespace character and false otherwise.
 */
bool RCPR_SYM(is_whitespace)(int ch);

/**
 * \brief Perform a left trim of the given string.
 *
 * Remove all whitespace on the left-hand side of the string up to the first
 * non-whitespace character.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to modify.
 */
void RCPR_SYM(left_trim)(char* str);

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
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(strdup)(char** output, RCPR_SYM(allocator)* alloc, const char* input);

/**
 * \brief Concatenate multiple strings into a single allocated string value.
 *
 * \note This function declaration is for documentation purposes. It isn't
 * actually implemented. Instead, an inline expansion of this function calls
 * \ref vstrctat. This inline function is imported, but attempting to call this
 * function by explicitly invoking its fully qualified symbolic name will cause
 * a linker error.
 *
 * On success, the string is allocated using the provided allocator. The caller
 * owns this string and must reclaim it using the same allocator instance when
 * it is no longer needed.
 *
 * \param output        Pointer to receive the concatenated string on success.
 * \param alloc         The allocator to use for this instance.
 * \param string1       The first string to concatenate.
 * \param ...           A NULL terminated list of all other strings to
 *                      concatenate.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(strcatv)(
    char** output, RCPR_SYM(allocator)* alloc, const char* string1, ...);

/**
 * \brief Varargs form of \ref strcatv.
 *
 * On success, the string is allocated using the provided allocator. The caller
 * owns this string and must reclaim it using the same allocator instance when
 * it is no longer needed.
 *
 * \param output        Pointer to receive the concatenated string on success.
 * \param alloc         The allocator to use for this instance.
 * \param string1       Teh first string to concatenate.
 * \param args          The varargs list (NULL terminated) of remaining strings
 *                      to concatenate.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(vstrcat)(
    char** output, RCPR_SYM(allocator)* alloc, const char* string1,
    va_list args);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_string_sym(sym) \
    RCPR_BEGIN_EXPORT \
    static inline bool \
    sym ## is_whitespace( \
        int x) { \
            return RCPR_SYM(is_whitespace)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## strdup( \
        char** x, RCPR_SYM(allocator)* y, const char* z) { \
            return RCPR_SYM(strdup)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## strcatv( \
        char** x, RCPR_SYM(allocator)* y, const char* z, ...) { \
            status retval; \
            va_list args; \
            va_start(args, z); \
            retval = RCPR_SYM(vstrcat)(x, y, z, args); \
            va_end(args); \
            return retval; \
    } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## vstrcat( \
        char** w, RCPR_SYM(allocator)* x, const char* y, va_list z) { \
            return RCPR_SYM(vstrcat)(w, x, y, z); \
    } \
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
