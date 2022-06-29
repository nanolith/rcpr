/**
 * \file test/string/test_strdup.cpp
 *
 * \brief Unit tests for RCPR strdup.
 */

#include <minunit/minunit.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_strdup);

RCPR_IMPORT_allocator;
RCPR_IMPORT_string_as(rcpr);
RCPR_IMPORT_resource;

/**
 * Verify that strdup checks its parameters.
 */
TEST(parameter_checks)
{
    allocator* alloc = nullptr;
    const char* INPUT = "test input";
    char* output = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* passing a null pointer to strdup causes it to fail. */
    TEST_EXPECT(
        ERROR_STRING_INVALID_PARAMETER ==
            rcpr_strdup(nullptr, alloc, INPUT));
    TEST_EXPECT(
        ERROR_STRING_INVALID_PARAMETER ==
            rcpr_strdup(&output, nullptr, INPUT));
    TEST_EXPECT(
        ERROR_STRING_INVALID_PARAMETER ==
            rcpr_strdup(&output, alloc, nullptr));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can duplicate an empty string.
 */
TEST(empty_string)
{
    allocator* alloc = nullptr;
    const char* INPUT = "";
    char* output = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* PRECONDITION: the output is NULL. */
    TEST_ASSERT(output == NULL);

    /* passing a null pointer to strdup causes it to fail. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&output, alloc, INPUT));

    /* the output should not be NULL. */
    TEST_ASSERT(output != NULL);

    /* verify that the two pointers do not match. */
    TEST_EXPECT(INPUT != output);

    /* verify that the length of the output is 0. */
    TEST_EXPECT(0 == strlen(output));

    /* verify that the two strings are equal. */
    TEST_EXPECT(0 == strcmp(INPUT, output));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, output));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can duplicate a non-empty string.
 */
TEST(happy_path)
{
    allocator* alloc = nullptr;
    const char* INPUT = "this is a test";
    char* output = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* PRECONDITION: the output is NULL. */
    TEST_ASSERT(output == NULL);

    /* passing a null pointer to strdup causes it to fail. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&output, alloc, INPUT));

    /* the output should not be NULL. */
    TEST_ASSERT(output != NULL);

    /* verify that the two pointers do not match. */
    TEST_EXPECT(INPUT != output);

    /* verify that the length of the output is equal to the input. */
    TEST_EXPECT(strlen(INPUT) == strlen(output));

    /* verify that the two strings are equal. */
    TEST_EXPECT(0 == strcmp(INPUT, output));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, output));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
