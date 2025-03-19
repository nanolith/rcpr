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

/**
 * \brief The string iterator is used for operations like \ref words.
 */
typedef struct RCPR_SYM(string_iterator) RCPR_SYM(string_iterator);

struct RCPR_SYM(string_iterator)
{
    char* startpos;
    char* endpos;
    bool (*token_fn)(int);
};

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

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(left_trim), char* str)
        /* str is a valid string. */
        RCPR_MODEL_CHECK_IS_STRING(str);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(left_trim))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(left_trim), char* str)
        /* str is a valid string. */
        RCPR_MODEL_CHECK_IS_STRING(str);
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(left_trim))

/**
 * \brief Perform a right trim of the given string.
 *
 * Remove all whitespace on the right-hand side of the string -- from the ASCII
 * zero to the first non-whitespace character -- are trimmed.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to modify.
 */
void RCPR_SYM(right_trim)(char* str);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(right_trim), char* str)
        /* str is a valid string. */
        RCPR_MODEL_CHECK_IS_STRING(str);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(right_trim))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(right_trim), char* str)
        /* str is a valid string. */
        RCPR_MODEL_CHECK_IS_STRING(str);
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(right_trim))

/**
 * \brief Perform a trim of the given string.
 *
 * Remove all whitespace on the left-hand and right-hand sides of the string.
 * All whitespace from the beginning of the string to the first non-whitespace
 * character and all whitespace from the end of the string to the last
 * non-whitespace character are removed.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to modify.
 */
void RCPR_SYM(trim)(char* str);

/**
 * \brief Initialize a string iterator to scan the given string for individual
 * words separated by one or more whitespace characters.
 *
 * During the first call, the first word is returned in \p word, and the \p
 * iterator argument is set up for subsequent calls. In the first call, \p str
 * should be set to the string to be scanned. This string will be modified by
 * this operation. During subsequent calls, \p str should be NULL; the
 * \p iterator argument will be used to extract subsequent words.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param word          Pointer to the character pointer to be set to the first
 *                      word on the first call or the next word on subsequent
 *                      calls. This word is a substring within the original
 *                      string, which is modified in this operation. It is a
 *                      substring of the original string and is NOT owned by the
 *                      caller.
 * \param iterator      The iterator to initialize for future calls if str is
 *                      NOT NULL or to use to get next words on subsequent
 *                      calls. The string iterator can be on the stack as it is
 *                      just a plain-old C structure. Its memory management is
 *                      up to the caller. This function only sets values in the
 *                      structure.
 * \param str           The string to scan for the first call or NULL for each
 *                      subsequent call.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_STRING_END_OF_INPUT when there are no more words to read.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(words)(
    const char** word, RCPR_SYM(string_iterator)* iterator, char* str);

/**
 * \brief Split a string into two halves based on the first occurrence of the
 * given character.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param lhs           Pointer to the character pointer to be set to the
 *                      left-hand side of the split.
 * \param rhs           Pointer to the character pointer to be set to the
 *                      right-hand side of the split.
 * \param str           The string to split.
 * \param delim         The delimiter character on which the string is split.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_STRING_END_OF_INPUT if the delimiter could not be found.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(split)(const char** lhs, const char** rhs, char* str, int delim);

/**
 * \brief Initialize a string iterator to scan the given string for individual
 * sequences separated by one or more occurrences of a token identified by the
 * given token function.
 *
 * This function works similarly to \ref words, except that the user can specify
 * a token matching function.
 *
 * During the first call, the first sequence is returned in \p seq, and the \p
 * iterator argument is set up for subsequent calls. In the first call, \p str
 * should be set to the string to be scanned. This string will be modified by
 * this operation. During subsequent calls, \p str should be NULL; the
 * \p iterator argument will be used to extract subsequent sequences.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param seq           Pointer to the character pointer to be set to the first
 *                      sequence on the first call or the next sequence on
 *                      subsequent calls. This sequence is a substring within
 *                      the original string, which is modified in this
 *                      operation. It is a substring of the original string and
 *                      is NOT owned by the caller.
 * \param iterator      The iterator to initialize for future calls if str is
 *                      NOT NULL or to use to get the next seq on subsequent
 *                      calls. The string iterator can be on the stack as it is
 *                      just a plain-old C structure. Its memory management is
 *                      up to the caller. This function only sets values in the
 *                      structure.
 * \param str           The string to scan for the first call or NULL for each
 *                      subsequent call.
 * \param token_fn      A function that returns true when the given character is
 *                      a break token for individual sequences, and false
 *                      otherwise.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_STRING_END_OF_INPUT when there are no more sequences to read.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(multisplit)(
    const char** seq, RCPR_SYM(string_iterator)* iterator, char* str,
    bool (*token_fn)(int));

/**
 * \brief Chomp a character off of the end of a string.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param str           The string to chomp.
 */
void RCPR_SYM(chomp)(char* str);

/**
 * \brief Return true if the given string starts with the given substring.
 *
 * \param str           The string to check.
 * \param substr        The substring to match at the beginning of \p str.
 *
 * \returns true if \p str starts with \p substr and false otherwise.
 */
bool RCPR_SYM(starts_with)(const char* str, const char* substr);

/**
 * \brief Return true if the given string ends with the given character.
 *
 * \param str           The string to check.
 * \param ch            The character to check.
 *
 * \returns true if the string ends with the given character and false
 * otherwise.
 */
bool RCPR_SYM(ends_with)(const char* str, int ch);

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
    typedef RCPR_SYM(string_iterator) sym ## string_iterator; \
    static inline bool \
    sym ## is_whitespace( \
        int x) { \
            return RCPR_SYM(is_whitespace)(x); } \
    static inline void \
    sym ## left_trim( \
        char* x) { \
            RCPR_SYM(left_trim)(x); } \
    static inline void \
    sym ## right_trim( \
        char* x) { \
            RCPR_SYM(right_trim)(x); } \
    static inline void \
    sym ## trim( \
        char* x) { \
            RCPR_SYM(trim)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## words( \
        const char** x, RCPR_SYM(string_iterator)* y, char* z) { \
            return RCPR_SYM(words)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## split( \
        const char** w, const char** x, char* y, int z) { \
            return RCPR_SYM(split)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## multisplit( \
        const char** w, RCPR_SYM(string_iterator)* x, char* y, \
        bool (*z)(int)) { \
            return RCPR_SYM(multisplit)(w,x,y,z); } \
    static inline void \
    sym ## chomp ( \
        char* x) { \
            RCPR_SYM(chomp)(x); } \
    static inline bool \
    sym ## starts_with(const char* x, const char* y) { \
            return RCPR_SYM(starts_with)(x,y); } \
    static inline bool \
    sym ## ends_with(const char* x, int y) { \
            return RCPR_SYM(ends_with)(x,y); } \
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
