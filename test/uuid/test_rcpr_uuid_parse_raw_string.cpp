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
TEST(blank_string)
{
    rcpr_uuid id;
    const char* STR = "123";

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_raw_string(
                &id, STR, strlen(STR)));
}
