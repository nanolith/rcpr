/**
 * \file test/fiber/test_fiber_scheduler_create_with_disciplines.cpp
 *
 * \brief Unit tests for fiber_scheduler_create_with_disciplines.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

TEST_SUITE(fiber_scheduler_create_with_disciplines);

/**
 * Verify that we can create a fiber scheduler instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a fiber scheduler with disciplines. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to release the fiber scheduler instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
