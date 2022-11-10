/**
 * \file test/string/test_trim.cpp
 *
 * \brief Unit tests for RCPR trim.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_trim);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that we can perform a trim on an empty string.
 */
TEST(trim_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* trim this string. */
    rcpr_trim(str);

    /* the string should still be empty. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Trimming a blank string creates an empty string.
 */
TEST(trim_blank_string)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "  \t\r\n\v  "));

    /* trim this string. */
    rcpr_trim(str);

    /* the string should be trimmed. */
    TEST_EXPECT(!strcmp(str, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Trim handles left trims.
 */
TEST(trim_left)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "   test"));

    /* trim this string. */
    rcpr_trim(str);

    /* the string should be trimmed. */
    TEST_EXPECT(!strcmp(str, "test"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Trim handles right trims.
 */
TEST(trim_right)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "test   "));

    /* trim this string. */
    rcpr_trim(str);

    /* the string should be trimmed. */
    TEST_EXPECT(!strcmp(str, "test"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Trim handles both sides.
 */
TEST(trim_both)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "   test   "));

    /* trim this string. */
    rcpr_trim(str);

    /* the string should be trimmed. */
    TEST_EXPECT(!strcmp(str, "test"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Trim ignores spaces in-between.
 */
TEST(trim_leaves_middle_spaces)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "   test it   "));

    /* trim this string. */
    rcpr_trim(str);

    /* the string should be trimmed. */
    TEST_EXPECT(!strcmp(str, "test it"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
