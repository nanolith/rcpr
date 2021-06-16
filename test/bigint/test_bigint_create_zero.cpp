/**
 * \file test/test_bigint_create_zero.cpp
 *
 * \brief Unit tests for bigint_create_zero.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/bigint.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(bigint_create_zero);

/**
 * Verify that we can create a bigint that is zero.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    bigint* i = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a zero bigint. */
    TEST_ASSERT(STATUS_SUCCESS == bigint_create_zero(&i, alloc, 2048));

    /* we should be able to release this bigint. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(bigint_resource_handle(i)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
