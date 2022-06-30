/**
 * \file test/string/test_vstrcat.cpp
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
 * In the happy path, strcatv concatenates strings.
 */
TEST(happy_path)
{
    allocator* alloc = nullptr;
    const char* INPUT1 = "This";
    const char* INPUT2 = " ";
    const char* INPUT3 = "works!";
    char* output = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* PRECONDITION: output is NULL. */
    TEST_ASSERT(nullptr == output);

    /* string concatenation works as expected. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_strcatv(&output, alloc, INPUT1, INPUT2, INPUT3, nullptr));

    /* POSTCONDITION: output is NOT NULL. */
    TEST_ASSERT(nullptr != output);

    /* This string should match our test strings put together. */
    TEST_EXPECT(0 == strcmp("This works!", output));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, output));
    TEST_ASSERT(
        STATUS_SUCCESS
            == resource_release(allocator_resource_handle(alloc)));
}
