/**
 * \file rcpr/uuid.h
 *
 * \brief The RCPR uuid library.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>
#include <stdint.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The \ref rcpr_uuid structure is a 16 byte unique identifier. Unlike
 * other types in RCPR, rcpr_uuid is typically stack allocated or is a value
 * type in a structure, as opposed to a pointer type. However, it is passed
 * around as a constant pointer to this value in functions.
 */
typedef struct rcpr_uuid rcpr_uuid;

struct rcpr_uuid
{
    uint8_t data[16];
};

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a C string from a \ref rcpr_uuid instance.
 *
 * \param str       Pointer to the character pointer to receive the string.
 * \param alloc     The allocator instance to use to allocate this string.
 * \param uuid      The \ref rcpr_uuid value to convert to a string.
 *
 * \note On success, the character pointer pointer is set to a C string
 * allocated by the allocator passed to this function. This is owned by the
 * caller and must be released by calling \ref allocator_reclaim on it when it
 * is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on succes.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if memory allocation fails.
 *
 * \pre
 *      - \p str must not reference a valid C string and must not be NULL.
 *      - \p alloc must reference a valid \ref allocator and must not be NULL.
 *      - \p uuid must reference a valid \ref rcpr_uuid value and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p str is set to a pointer to a valid C-string, which is
 *        owned by the caller and must be reclaimed by \ref allocator_reclaim
 *        when no longer needed.
 *      - On failure, \p str is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
rcpr_uuid_to_string(
    char** str, allocator* alloc, const rcpr_uuid* uuid);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Convert a string value into a \ref rcpr_uuid value.
 *
 * \param uuid      Pointer to the \ref rcpr_uuid value to which the parsed UUID
 *                  is stored.
 * \param str       The character string to parse.
 *
 * \note Unlike other RCPR functions, this does an IN-PLACE copy of the UUID
 * value into the \ref rcpr_uuid value type.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on succes.
 *      - ERROR_UUID_PARSING_FAILED if the parsing of a UUID value from the
 *        string failed.
 *
 * \pre
 *      - \p uuid must point to a \ref rcpr_uuid value that can be overwritten
 *        by this function. It must not be NULL.
 *      - \p str must point to a valid C-string.
 *
 * \post
 *      - On success, the value pointed to by \p uuid is overwritten by the
 *        parsed UUID value from \p str.
 *      - On failure, \p uuid is not changed, and an error status is returned.
 */
status FN_DECL_MUST_CHECK
rcpr_uuid_parse_string(
    rcpr_uuid* uuid, const char* str);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref rcpr_uuid property.
 *
 * \param id            The \ref rcpr_uuid instance to be verified.
 *
 * \returns true if the \ref rcpr_uuid instance is valid.
 */
bool prop_uuid_valid(const rcpr_uuid* id);

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
