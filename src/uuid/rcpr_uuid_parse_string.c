/**
 * \file uuid/rcpr_uuid_to_string.c
 *
 * \brief Parse a UUID from a string.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/uuid.h>
#include <string.h>

/* forward decls. */
static bool try_read_hex_nibble(const char** str, uint8_t* byte);
static bool try_read_hex_byte(const char** str, uint8_t* byte);
static bool try_read_dash(const char** str, uint8_t* byte);

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
    rcpr_uuid* uuid, const char* str)
{
    uint8_t ignore;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_uuid_valid(uuid));
    MODEL_ASSERT(NULL != str);

    /* verify that the string is not NULL. */
    if (NULL == str) goto fail;

    /* read the first four byte values. */
    if (!try_read_hex_byte(&str, uuid->data +  0)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data +  1)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data +  2)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data +  3)) goto fail;

    /* read the first dash. */
    if (!try_read_dash(&str, &ignore)) goto fail;

    /* read the next two bytes. */
    if (!try_read_hex_byte(&str, uuid->data +  4)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data +  5)) goto fail;

    /* read the second dash. */
    if (!try_read_dash(&str, &ignore)) goto fail;

    /* read the next two bytes. */
    if (!try_read_hex_byte(&str, uuid->data +  6)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data +  7)) goto fail;

    /* read the third dash. */
    if (!try_read_dash(&str, &ignore)) goto fail;

    /* read the next two bytes. */
    if (!try_read_hex_byte(&str, uuid->data +  8)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data +  9)) goto fail;

    /* read the fourth dash. */
    if (!try_read_dash(&str, &ignore)) goto fail;

    /* read the last six bytes. */
    if (!try_read_hex_byte(&str, uuid->data + 10)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data + 11)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data + 12)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data + 13)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data + 14)) goto fail;
    if (!try_read_hex_byte(&str, uuid->data + 15)) goto fail;

    /* finally, if the string is not empty, this fails. */
    if (0 != *str) goto fail;

    /* if we've made it here, we've successfully parsed a uuid string. */
    return STATUS_SUCCESS;

fail:
    return ERROR_UUID_PARSING_FAILED;
}

/**
 * \brief Try to read a hex nibble from a string in the form of X, where X is a
 * hex digit between 0-9 or a-f A-F.
 *
 * \param str       Pointer to the string pointer containing the input string.
 *                  The pointer is updated with the digit read on success.
 * \param byte      Pointer to the uint8_t value to be updated with this hex
 *                  nibble.
 *
 * \returns true if the read succeeded, and false otherwise.
 */
static bool try_read_hex_nibble(const char** str, uint8_t* byte)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != str);
    MODEL_ASSERT(NULL != byte);

    uint8_t in = *(*str);

    switch (in)
    {
        case '0': case '1': case '2': case '3': case '4':
        case '5': case '6': case '7': case '8': case '9':
            *byte = in - '0';
            *str += 1;
            return true;

        case 'A': case 'B': case 'C': case 'D': case 'E': case 'F':
            *byte = in - 'A' + 10;
            *str += 1;
            return true;

        case 'a': case 'b': case 'c': case 'd': case 'e': case 'f':
            *byte = in - 'a' + 10;
            *str += 1;
            return true;

        default:
            return false;
    }
}

/**
 * \brief Try to read a hex byte from a string in the form of XX, where X is a
 * hex digit between 0-9 or a-f A-F.
 *
 * \param str       Pointer to the string pointer containing the input string.
 *                  The pointer is updated with the digits read on success.
 * \param byte      Pointer to the uint8_t value to be updated with this hex
 *                  byte.
 *
 * \returns true if the read succeeded, and false otherwise.
 */
static bool try_read_hex_byte(const char** str, uint8_t* byte)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != str);
    MODEL_ASSERT(NULL != byte);

    const char* in = *str;

    uint8_t high_nibble;
    uint8_t low_nibble;

    if (!try_read_hex_nibble(&in, &high_nibble)) goto fail;
    if (!try_read_hex_nibble(&in, &low_nibble)) goto fail;

    /* success. */
    *byte = (high_nibble << 4) | low_nibble;
    *str += 2;
    return true;

fail:
    return false;
}

/**
 * \brief Try to read a dash from a string in the form of -.
 *
 * \param str       Pointer to the string pointer containing the input string.
 *                  The pointer is updated with the dash read on success.
 * \param byte      Pointer to the uint8_t value to be updated with the dash.
 *
 * \returns true if the read succeeded, and false otherwise.
 */
static bool try_read_dash(const char** str, uint8_t* byte)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != str);
    MODEL_ASSERT(NULL != byte);

    if (*(*str) == '-')
    {
        /* success. */
        *byte = '-';
        *str += 1;
        return true;
    }
    else
    {
        return false;
    }
}
