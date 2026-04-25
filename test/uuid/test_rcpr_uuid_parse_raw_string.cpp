/**
 * \file test/uuid/test_rcpr_uuid_parse_raw_string.cpp
 *
 * \brief Unit tests for rcpr_uuid_parse_raw_string.
 */

#include <minunit/minunit.h>
#include <rcpr/uuid.h>
#include <string.h>

RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

TEST_SUITE(rcpr_uuid_parse_raw_string);

/**
 * The empty string fails to parse.
 */
TEST(null_string)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_raw_string(
                &id, nullptr, 36));
}

/**
 * A string smaller than 36 bytes fails to parse.
 */
TEST(small_string)
{
    rcpr_uuid id;
    const char* STR = "123";

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_raw_string(
                &id, STR, strlen(STR)));
}

/**
 * A string larger than 36 bytes fails to parse.
 */
TEST(large_string)
{
    rcpr_uuid id;
    const char* STR = "a8362615-46f1-46ff-9ce3-f43249145d57---";
    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_raw_string(
                &id, STR, strlen(STR)));
}

/**
 * Happy path.
 */
TEST(happy_path)
{
    rcpr_uuid id;
    const char* STR = "a8362615-46f1-46ff-9ce3-f43249145d57";
    const rcpr_uuid EXPECTED_UUID = { .data = {
        0xa8, 0x36, 0x26, 0x15, 0x46, 0xf1, 0x46, 0xff,
        0x9c, 0xe3, 0xf4, 0x32, 0x49, 0x14, 0x5d, 0x57 } };

    TEST_ASSERT(
        STATUS_SUCCESS ==
            rcpr_uuid_parse_raw_string(
                &id, STR, strlen(STR)));

    TEST_EXPECT(!memcmp(&id, &EXPECTED_UUID, sizeof(id)));
}
