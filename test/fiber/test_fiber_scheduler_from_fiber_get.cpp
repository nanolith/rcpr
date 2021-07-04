/**
 * \file test/fiber/test_fiber_scheduler_from_fiber_get.cpp
 *
 * \brief Unit tests for fiber_scheduler_from_fiber_get.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

TEST_SUITE(fiber_create_for_thread);

/**
 * Verify that we can get the fiber scheduler assigned to a fiber.
 */
TEST(get_scheduler)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* f = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create a fiber for a thread. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_create_for_thread(&f, sched, alloc));

    /* we should be able to get the fiber scheduler for this fiber. */
    TEST_EXPECT(sched == fiber_scheduler_from_fiber_get(f));

    /* we should be able to release the fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_resource_handle(f)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
