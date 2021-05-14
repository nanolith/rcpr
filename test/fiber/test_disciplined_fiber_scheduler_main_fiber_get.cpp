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
TEST(add)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* fib = nullptr;
    rcpr_uuid id = { .data = {
        0x0e, 0x2c, 0xfc, 0x92, 0x89, 0xfa, 0x46, 0x54,
        0xb9, 0x69, 0xd7, 0x1b, 0x18, 0x46, 0x9b, 0x4c } };
    fiber_scheduler_discipline_callback_fn emptyvec[0];
    fiber_scheduler_disciplined_context* ctx;

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
