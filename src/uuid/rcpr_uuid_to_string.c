/**
 * \file uuid/rcpr_uuid_to_string.c
 *
 * \brief Convert a UUID to a C string.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/uuid.h>
#include <string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_uuid;

#define UUID_STRING_LENGTH 36

/**
 * \brief Return the low nibble of the given byte.
 *
 * \param b     The byte to convert.
 *
 * \returns the low nibble.
 */
static inline uint8_t low_nibble(uint8_t b)
{
    return b & 0x0F;
}

/**
 * \brief Return the high nibble of the given byte.
 *
 * \param b     The byte to convert.
 *
 * \returns the high nibble.
 */
static inline uint8_t high_nibble(uint8_t b)
{
    return (b & 0xF0) >> 4;
}

/**
 * \brief Convert a nibble to a printable hex character.
 *
 * \param nibble    The nibble to convert.
 *
 * \returns a printable hex representation of the nibble.
 */
static inline char nibble_to_hex(char nibble)
{
    MODEL_ASSERT(nibble >= 0 && nibble <= 15);

    switch (nibble)
    {
        case 0:
        case 1:
        case 2:
        case 3:
        case 4:
        case 5:
        case 6:
        case 7:
        case 8:
        case 9:
            return nibble + '0';

        default:
            return nibble - 10 + 'a';
    }
}

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
RCPR_SYM(rcpr_uuid_to_string)(
    char** str, RCPR_SYM(allocator)* alloc, const RCPR_SYM(rcpr_uuid)* uuid)
{
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != str);
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(prop_uuid_valid(uuid));

    /* attempt to allocate a buffer to hold our string value. */
    retval = allocator_allocate(alloc, (void**)str, UUID_STRING_LENGTH + 1);
    if (STATUS_SUCCESS != retval)
    {
        *str = NULL;
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    /* build the string. */
    char* tmp = *str;
    tmp[ 0] = nibble_to_hex(high_nibble(uuid->data[ 0]));
    tmp[ 1] = nibble_to_hex(low_nibble( uuid->data[ 0]));
    tmp[ 2] = nibble_to_hex(high_nibble(uuid->data[ 1]));
    tmp[ 3] = nibble_to_hex(low_nibble( uuid->data[ 1]));
    tmp[ 4] = nibble_to_hex(high_nibble(uuid->data[ 2]));
    tmp[ 5] = nibble_to_hex(low_nibble( uuid->data[ 2]));
    tmp[ 6] = nibble_to_hex(high_nibble(uuid->data[ 3]));
    tmp[ 7] = nibble_to_hex(low_nibble( uuid->data[ 3]));
    tmp[ 8] = '-';
    tmp[ 9] = nibble_to_hex(high_nibble(uuid->data[ 4]));
    tmp[10] = nibble_to_hex(low_nibble( uuid->data[ 4]));
    tmp[11] = nibble_to_hex(high_nibble(uuid->data[ 5]));
    tmp[12] = nibble_to_hex(low_nibble( uuid->data[ 5]));
    tmp[13] = '-';
    tmp[14] = nibble_to_hex(high_nibble(uuid->data[ 6]));
    tmp[15] = nibble_to_hex(low_nibble( uuid->data[ 6]));
    tmp[16] = nibble_to_hex(high_nibble(uuid->data[ 7]));
    tmp[17] = nibble_to_hex(low_nibble( uuid->data[ 7]));
    tmp[18] = '-';
    tmp[19] = nibble_to_hex(high_nibble(uuid->data[ 8]));
    tmp[20] = nibble_to_hex(low_nibble( uuid->data[ 8]));
    tmp[21] = nibble_to_hex(high_nibble(uuid->data[ 9]));
    tmp[22] = nibble_to_hex(low_nibble( uuid->data[ 9]));
    tmp[23] = '-';
    tmp[24] = nibble_to_hex(high_nibble(uuid->data[10]));
    tmp[25] = nibble_to_hex(low_nibble( uuid->data[10]));
    tmp[26] = nibble_to_hex(high_nibble(uuid->data[11]));
    tmp[27] = nibble_to_hex(low_nibble( uuid->data[11]));
    tmp[28] = nibble_to_hex(high_nibble(uuid->data[12]));
    tmp[29] = nibble_to_hex(low_nibble( uuid->data[12]));
    tmp[30] = nibble_to_hex(high_nibble(uuid->data[13]));
    tmp[31] = nibble_to_hex(low_nibble( uuid->data[13]));
    tmp[32] = nibble_to_hex(high_nibble(uuid->data[14]));
    tmp[33] = nibble_to_hex(low_nibble( uuid->data[14]));
    tmp[34] = nibble_to_hex(high_nibble(uuid->data[15]));
    tmp[35] = nibble_to_hex(low_nibble( uuid->data[15]));
    tmp[36] = 0;

    return STATUS_SUCCESS;
}
