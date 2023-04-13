/**
 * \file test/string/test_starts_with.cpp
 *
 * \brief Unit tests for RCPR starts_with.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

TEST_SUITE(starts_with);

/**
 * starts_with with both NULL arguments returns true.
 */
TEST(double_null)
{
    TEST_ASSERT(true == rcpr_starts_with(nullptr, nullptr));
}

/**
 * If substr is NULL, it always returns true.
 */
TEST(substr_null)
{
    TEST_ASSERT(true == rcpr_starts_with("any string", nullptr));
}

/**
 * If str is NULL and substr is NOT, then it always returns false.
 */
TEST(str_null)
{
    TEST_ASSERT(false == rcpr_starts_with(NULL, "any string"));
}

/**
 * If str is shorter than substr, then it returns false.
 */
TEST(str_shorter)
{
    TEST_ASSERT(false == rcpr_starts_with("any", "any string"));
}

/**
 * If str starts with substr, then it returns true.
 */
TEST(str_starts_with_substr)
{
    TEST_ASSERT(true == rcpr_starts_with("abcdef", "abc"));
}

/**
 * If str does not start with substr, then it returns false.
 */
TEST(str_does_not_start_with_substr)
{
    TEST_ASSERT(false == rcpr_starts_with("abcdef", "abx"));
}
