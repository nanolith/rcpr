/**
 * \file test/string/test_split.cpp
 *
 * \brief Unit tests for RCPR split.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_split);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that split fails as expected on an empty string.
 */
TEST(split_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* lhs = nullptr;
    const char* rhs = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* perform split on this string. */
    TEST_ASSERT(ERROR_STRING_END_OF_INPUT == rcpr_split(&lhs, &rhs, str, ';'));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that split fails as expected when delim is not found.
 */
TEST(split_delim_not_found)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* lhs = nullptr;
    const char* rhs = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "missing delim"));

    /* perform split on this string. */
    TEST_ASSERT(ERROR_STRING_END_OF_INPUT == rcpr_split(&lhs, &rhs, str, ';'));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * When delim is found, both lhs and rhs point to the respective halves of the
 * string.
 */
TEST(split_base_case)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* lhs = nullptr;
    const char* rhs = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "left;right"));

    /* perform split on this string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_split(&lhs, &rhs, str, ';'));
    TEST_EXPECT(!strcmp(lhs, "left"));
    TEST_EXPECT(!strcmp(rhs, "right"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * When delim is found at the end of the string, then rhs is empty.
 */
TEST(split_delim_at_end)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* lhs = nullptr;
    const char* rhs = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "left;"));

    /* perform split on this string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_split(&lhs, &rhs, str, ';'));
    TEST_EXPECT(!strcmp(lhs, "left"));
    TEST_EXPECT(!strcmp(rhs, ""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * When delim occurs multiple times, rhs contains the other delims.
 */
TEST(split_delim_multiple)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* lhs = nullptr;
    const char* rhs = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "left;right;again"));

    /* perform split on this string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_split(&lhs, &rhs, str, ';'));
    TEST_EXPECT(!strcmp(lhs, "left"));
    TEST_EXPECT(!strcmp(rhs, "right;again"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
