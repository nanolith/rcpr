/**
 * \file test/string/test_ends_with.cpp
 *
 * \brief Unit tests for RCPR ends_with.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

TEST_SUITE(ends_with);

/**
 * ends_with on an empty string returns false.
 */
TEST(empty_string)
{
    TEST_ASSERT(false == rcpr_ends_with("", 'Z'));
}


/**
 * If the only character is the matching character, ends_with returns true.
 */
TEST(singleton_match)
{
    TEST_ASSERT(true == rcpr_ends_with("Z", 'Z'));
}

/**
 * If the only character is NOT the matching character, ends_with returns false.
 */
TEST(singleton_no_match)
{
    TEST_ASSERT(false == rcpr_ends_with("A", 'Z'));
}

/**
 * If a string with multiple characters matches, true is returned.
 */
TEST(multi_match)
{
    TEST_ASSERT(true == rcpr_ends_with("testZ", 'Z'));
}

/**
 * If a string with multiple characters doesn't match, false is returned.
 */
TEST(multi_no_match)
{
    TEST_ASSERT(false == rcpr_ends_with("test", 'Z'));
}

/**
 * If the string contains the character but not at the end, this does not match.
 */
TEST(contains_not_at_end)
{
    TEST_ASSERT(false == rcpr_ends_with("ZYXW", 'Z'));
}

/**
 * If a string matches multiple times, true is returned only if the end matches.
 */
TEST(multi_match_end)
{
    TEST_ASSERT(true == rcpr_ends_with("ZZZ", 'Z'));
}

/**
 * If a string matches multiple times, true is returned only if the end matches.
 */
TEST(multi_no_match_end)
{
    TEST_ASSERT(false == rcpr_ends_with("ZZZ.", 'Z'));
}
