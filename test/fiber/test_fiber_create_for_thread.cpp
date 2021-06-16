/**
 * \file test/fiber/test_fiber_create_for_thread.cpp
 *
 * \brief Unit tests for fiber_create_for_thread.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

TEST_SUITE(fiber_create_for_thread);

/**
 * Verify that we can create and release a fiber instance created for a thread.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber* f = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a fiber for a thread. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_create_for_thread(&f, alloc));

    /* we should be able to release the fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_resource_handle(f)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
