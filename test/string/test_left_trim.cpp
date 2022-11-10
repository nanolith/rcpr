/**
 * \file test/string/test_left_trim.cpp
 *
 * \brief Unit tests for RCPR left_trim.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_left_trim);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that we can perform a left trim on an empty string.
 */
TEST(left_trim_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* left trim this string. */
    rcpr_left_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that left_trim removes all whitespace in a string of only whitespace.
 */
TEST(left_trim_blank_string)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "  \t\r\n  \v  "));

    /* left trim this string. */
    rcpr_left_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that left_trim removes all whitespace before a word.
 */
TEST(left_trim_simple_word)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "  test"));

    /* left trim this string. */
    rcpr_left_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, "test"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that left_trim ignores all spaces after the first non-space character.
 */
TEST(left_trim_only_left_whitespace)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "   a   "));

    /* left trim this string. */
    rcpr_left_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, "a   "));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
