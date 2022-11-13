/**
 * \file test/string/test_chomp.cpp
 *
 * \brief Unit tests for RCPR chomp.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_chomp);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that chomp does nothing with an empty string.
 */
TEST(chomp_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* perform chomp on this string. */
    rcpr_chomp(str);

    /* the string is still empty. */
    TEST_EXPECT(!strcmp(str,""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that chomp removes the last character from a string.
 */
TEST(chomp_base_case)
{
    allocator* alloc = nullptr;
    char* str = nullptr;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "test"));

    /* perform chomp on this string. */
    rcpr_chomp(str);

    /* the last character was chomped. */
    TEST_EXPECT(!strcmp(str,"tes"));

    /* perform chomp on this string. */
    rcpr_chomp(str);

    /* the last character was chomped. */
    TEST_EXPECT(!strcmp(str,"te"));

    /* perform chomp on this string. */
    rcpr_chomp(str);

    /* the last character was chomped. */
    TEST_EXPECT(!strcmp(str,"t"));

    /* perform chomp on this string. */
    rcpr_chomp(str);

    /* the string is empty. */
    TEST_EXPECT(!strcmp(str,""));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
