/**
 * \file test/uuid/test_rcpr_uuid_parse_string.cpp
 *
 * \brief Unit tests for rcpr_uuid_parse_string.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/uuid.h>
#include <string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(rcpr_uuid_parse_string);

/**
 * The empty string fails to parse.
 */
TEST(null_string)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, nullptr));
}

/**
 * A blank string fails to parse.
 */
TEST(blank_string)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, ""));
}

/**
 * a non-hex character for the first character fails to parse.
 */
TEST(first_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, ","));
}

/**
 * a non-hex character for the second character fails to parse.
 */
TEST(second_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "0,"));
}

/**
 * No character for the second character fails to parse.
 */
TEST(second_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "0"));
}

/**
 * a non-hex character for the third character fails to parse.
 */
TEST(third_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00,"));
}

/**
 * No character for the third character fails to parse.
 */
TEST(third_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00"));
}

/**
 * a non-hex character for the fourth character fails to parse.
 */
TEST(fourth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "000,"));
}

/**
 * No character for the fourth character fails to parse.
 */
TEST(fourth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "000"));
}

/**
 * a non-hex character for the fifth character fails to parse.
 */
TEST(fifth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "0000,"));
}

/**
 * No character for the fifth character fails to parse.
 */
TEST(fifth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "0000"));
}

/**
 * a non-hex character for the sixth character fails to parse.
 */
TEST(sixth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000,"));
}

/**
 * No character for the sixth character fails to parse.
 */
TEST(sixth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000"));
}

/**
 * a non-hex character for the seventh character fails to parse.
 */
TEST(seventh_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "000000,"));
}

/**
 * No character for the seventh character fails to parse.
 */
TEST(seventh_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "000000"));
}

/**
 * a non-hex character for the eighth character fails to parse.
 */
TEST(eighth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "0000000,"));
}

/**
 * No character for the eighth character fails to parse.
 */
TEST(eighth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "0000000"));
}

/**
 * a non-dash character for the ninth character fails to parse.
 */
TEST(ninth_nodash)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "000000000"));
}

/**
 * No character for the ninth character fails to parse.
 */
TEST(ninth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000"));
}

/**
 * a non-hex character for the tenth character fails to parse.
 */
TEST(tenth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-,"));
}

/**
 * No character for the tenth character fails to parse.
 */
TEST(tenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-"));
}

/**
 * a non-hex character for the eleventh character fails to parse.
 */
TEST(eleventh_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0,"));
}

/**
 * No character for the eleventh character fails to parse.
 */
TEST(eleventh_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0"));
}

/**
 * a non-hex character for the twelvth character fails to parse.
 */
TEST(twelvth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-00,"));
}

/**
 * No character for the twelvth character fails to parse.
 */
TEST(twelvth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-00"));
}

/**
 * a non-hex character for the thirteenth character fails to parse.
 */
TEST(thirteenth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-000,"));
}

/**
 * No character for the thirteenth character fails to parse.
 */
TEST(thirteenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-000"));
}

/**
 * a non-dash character for the fourteenth character fails to parse.
 */
TEST(fourteenth_nodash)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000,"));
}

/**
 * No character for the fourteenth character fails to parse.
 */
TEST(fourteenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000"));
}

/**
 * a non-hex character for the fifteenth character fails to parse.
 */
TEST(fifteenth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-,"));
}

/**
 * No character for the fifteenth character fails to parse.
 */
TEST(fifteenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-"));
}

/**
 * a non-hex character for the sixteenth character fails to parse.
 */
TEST(sixteenth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0,"));
}

/**
 * No character for the sixteenth character fails to parse.
 */
TEST(sixteenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0"));
}

/**
 * a non-hex character for the seventeenth character fails to parse.
 */
TEST(seventeenth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-00,"));
}

/**
 * No character for the seventeenth character fails to parse.
 */
TEST(seventeenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-00"));
}

/**
 * a non-hex character for the eighteenth character fails to parse.
 */
TEST(eighteenth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-000,"));
}

/**
 * No character for the eighteenth character fails to parse.
 */
TEST(eighteenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-000"));
}

/**
 * a non-dash character for the nineteenth character fails to parse.
 */
TEST(nineteenth_nodash)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000,"));
}

/**
 * No character for the nineteenth character fails to parse.
 */
TEST(nineteenth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000"));
}

/**
 * a non-hex character for the twentieth character fails to parse.
 */
TEST(twentieth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-,"));
}

/**
 * No character for the twentieth character fails to parse.
 */
TEST(twentieth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-"));
}

/**
 * a non-hex character for the twenty-first character fails to parse.
 */
TEST(twenty_first_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0,"));
}

/**
 * No character for the twenty-first character fails to parse.
 */
TEST(twenty_first_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0"));
}

/**
 * a non-hex character for the twenty-second character fails to parse.
 */
TEST(twenty_second_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-00,"));
}

/**
 * No character for the twenty-second character fails to parse.
 */
TEST(twenty_second_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-00"));
}

/**
 * a non-hex character for the twenty-third character fails to parse.
 */
TEST(twenty_third_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-000,"));
}

/**
 * No character for the twenty-third character fails to parse.
 */
TEST(twenty_third_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-000"));
}

/**
 * a non-dash character for the twenty-fourth character fails to parse.
 */
TEST(twenty_fourth_nodash)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000,"));
}

/**
 * No character for the twenty-fourth character fails to parse.
 */
TEST(twenty_fourth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000"));
}

/**
 * a non-hex character for the twenty-fifth character fails to parse.
 */
TEST(twenty_fifth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-,"));
}

/**
 * No character for the twenty-fifth character fails to parse.
 */
TEST(twenty_fifth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-"));
}

/**
 * a non-hex character for the twenty-sixth character fails to parse.
 */
TEST(twenty_sixth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0,"));
}

/**
 * No character for the twenty-sixth character fails to parse.
 */
TEST(twenty_sixth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0"));
}

/**
 * a non-hex character for the twenty-seventh character fails to parse.
 */
TEST(twenty_seventh_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00,"));
}

/**
 * No character for the twenty-seventh character fails to parse.
 */
TEST(twenty_seventh_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00"));
}

/**
 * a non-hex character for the twenty-eighth character fails to parse.
 */
TEST(twenty_eighth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000,"));
}

/**
 * No character for the twenty-eighth character fails to parse.
 */
TEST(twenty_eighth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000"));
}

/**
 * a non-hex character for the twenty-ninth character fails to parse.
 */
TEST(twenty_ninth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0000,"));
}

/**
 * No character for the twenty-ninth character fails to parse.
 */
TEST(twenty_ninth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0000"));
}

/**
 * a non-hex character for the thirtieth character fails to parse.
 */
TEST(thirtieth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00000,"));
}

/**
 * No character for the thirtieth character fails to parse.
 */
TEST(thirtieth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00000"));
}

/**
 * a non-hex character for the thirty-first character fails to parse.
 */
TEST(thirty_first_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000000,"));
}

/**
 * No character for the thirty-first character fails to parse.
 */
TEST(thirty_first_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000000"));
}

/**
 * a non-hex character for the thirty-second character fails to parse.
 */
TEST(thirty_second_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0000000,"));
}

/**
 * No character for the thirty-second character fails to parse.
 */
TEST(thirty_second_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0000000"));
}

/**
 * a non-hex character for the thirty-third character fails to parse.
 */
TEST(thirty_third_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00000000,"));
}

/**
 * No character for the thirty-third character fails to parse.
 */
TEST(thirty_third_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00000000"));
}

/**
 * a non-hex character for the thirty-fourth character fails to parse.
 */
TEST(thirty_fourth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000000000,"));
}

/**
 * No character for the thirty-fourth character fails to parse.
 */
TEST(thirty_fourth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000000000"));
}

/**
 * a non-hex character for the thirty-fifth character fails to parse.
 */
TEST(thirty_fifth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0000000000,"));
}

/**
 * No character for the thirty-fifth character fails to parse.
 */
TEST(thirty_fifth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-0000000000"));
}

/**
 * a non-hex character for the thirty-sixth character fails to parse.
 */
TEST(thirty_sixth_nonhex)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00000000000,"));
}

/**
 * No character for the thirty-sixth character fails to parse.
 */
TEST(thirty_sixth_blank)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-00000000000"));
}

/**
 * Extra characters after the uuid string cause the parse to fail.
 */
TEST(extra_characters)
{
    rcpr_uuid id;

    TEST_ASSERT(
        STATUS_SUCCESS !=
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000000000000w"));
}

/**
 * We can parse a zero uuid.
 */
TEST(zero_uuid)
{
    rcpr_uuid id;
    const rcpr_uuid EXPECTED_ID = { .data = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } };

    /* PRECONDITION: fill the id with garbage. */
    memset(&id, 'a', sizeof(id));

    /* parse the zero uuid string. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rcpr_uuid_parse_string(
                &id, "00000000-0000-0000-0000-000000000000"));

    /* POSTCONDITION: the uuid matches the expected ID. */
    TEST_EXPECT(!memcmp(&id, &EXPECTED_ID, sizeof(id)));
}

/**
 * We can parse an arbitrary lowercase uuid.
 */
TEST(arbitrary_lowercase_uuid)
{
    rcpr_uuid id;
    const rcpr_uuid EXPECTED_ID = { .data = {
        0xd3, 0x9d, 0x39, 0x77, 0xc6, 0x71, 0x40, 0x36,
        0x89, 0xd1, 0xfa, 0x24, 0x62, 0x1d, 0x70, 0x42 } };

    /* PRECONDITION: fill the id with garbage. */
    memset(&id, 'a', sizeof(id));

    /* parse the zero uuid string. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rcpr_uuid_parse_string(
                &id, "d39d3977-c671-4036-89d1-fa24621d7042"));

    /* POSTCONDITION: the uuid matches the expected ID. */
    TEST_EXPECT(!memcmp(&id, &EXPECTED_ID, sizeof(id)));
}

/**
 * We can parse an arbitrary uppercase uuid.
 */
TEST(arbitrary_uppercase_uuid)
{
    rcpr_uuid id;
    const rcpr_uuid EXPECTED_ID = { .data = {
        0xd3, 0x9d, 0x39, 0x77, 0xc6, 0x71, 0x40, 0x36,
        0x89, 0xd1, 0xfa, 0x24, 0x62, 0x1d, 0x70, 0x42 } };

    /* PRECONDITION: fill the id with garbage. */
    memset(&id, 'a', sizeof(id));

    /* parse the zero uuid string. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rcpr_uuid_parse_string(
                &id, "D39D3977-C671-4036-89D1-FA24621D7042"));

    /* POSTCONDITION: the uuid matches the expected ID. */
    TEST_EXPECT(!memcmp(&id, &EXPECTED_ID, sizeof(id)));
}
