/**
 * \file test/string/test_right_trim.cpp
 *
 * \brief Unit tests for RCPR right_trim.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_right_trim);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that we can perform a right trim on an empty string.
 */
TEST(right_trim_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* right trim this string. */
    rcpr_right_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform a right trim on a single space string.
 */
TEST(right_trim_single_space)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, " "));

    /* right trim this string. */
    rcpr_right_trim(str);

    /* the string should be right trimmed. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform a right trim on a string of white spaces.
 */
TEST(right_trim_blank_string)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "  \t\r\n  \v   "));

    /* right trim this string. */
    rcpr_right_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform a right trim on a single character string.
 */
TEST(right_trim_single_char)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "a"));

    /* right trim this string. */
    rcpr_right_trim(str);

    /* the string should be right trimmed. */
    TEST_EXPECT(!strcmp(str, "a"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform a right trim on a string with a single character
 * and spaces.
 */
TEST(right_trim_single_char_spaces)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "a        "));

    /* right trim this string. */
    rcpr_right_trim(str);

    /* the string should be right trimmed. */
    TEST_EXPECT(!strcmp(str, "a"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform a right trim on an arbitrary string with a CR at
 * the end (e.g. like HTTP).
 */
TEST(right_trim_http_example)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "GET / HTTP/1.1\r"));

    /* right trim this string. */
    rcpr_right_trim(str);

    /* the string should be right trimmed. */
    TEST_EXPECT(!strcmp(str, "GET / HTTP/1.1"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
