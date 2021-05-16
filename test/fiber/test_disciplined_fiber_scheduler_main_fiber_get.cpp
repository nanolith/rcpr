/**
 * \file test/fiber/test_disciplined_fiber_scheduler_main_fiber_get.cpp
 *
 * \brief Unit tests for disciplined_fiber_scheduler_main_fiber_get.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

#include "../../src/fiber/common/fiber_internal.h"

TEST_SUITE(disciplined_fiber_scheduler_main_fiber_get);

/**
 * Verify that we can get the main fiber.
 */
TEST(get)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* fib = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to get the main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_main_fiber_get(
                &fib, sched));

    /* The fiber should not be null. */
    TEST_EXPECT(nullptr != fib);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
