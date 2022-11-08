/**
 * \file test/string/test_is_whitespace.cpp
 *
 * \brief Unit tests for RCPR is_whitespace.
 */

#include <minunit/minunit.h>
#include <rcpr/string.h>

TEST_SUITE(string_is_whitespace);

RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that is_whitespace returns true for ' '.
 */
TEST(is_whitespace_space)
{
    TEST_ASSERT(rcpr_is_whitespace(' '));
}

/**
 * Verify that is_whitespace returns true for '\t'.
 */
TEST(is_whitespace_tab)
{
    TEST_ASSERT(rcpr_is_whitespace('\t'));
}

/**
 * Verify that is_whitespace returns true for '\n'.
 */
TEST(is_whitespace_lf)
{
    TEST_ASSERT(rcpr_is_whitespace('\n'));
}

/**
 * Verify that is_whitespace returns true for '\v'.
 */
TEST(is_whitespace_vt)
{
    TEST_ASSERT(rcpr_is_whitespace('\v'));
}

/**
 * Verify that is_whitespace returns true for '\f'.
 */
TEST(is_whitespace_ff)
{
    TEST_ASSERT(rcpr_is_whitespace('\f'));
}

/**
 * Verify that is_whitespace returns true for '\r'.
 */
TEST(is_whitespace_cr)
{
    TEST_ASSERT(rcpr_is_whitespace('\r'));
}
