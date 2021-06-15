/**
 * \file test/fiber/test_disciplined_fiber_scheduler_set_idle_fiber.cpp
 *
 * \brief Unit tests for disciplined_fiber_scheduler_set_idle_fiber.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

#include "../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(disciplined_fiber_scheduler_set_idle_fiber);

/**
 * Verify that we can set the idle fiber.
 */
TEST(basics)
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

    /* we should be able to create a dummy thread fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create_for_thread(&fib, alloc));

    /* PRECONDITION: the idle fiber is NOT set. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;
    TEST_ASSERT(nullptr == ctx->idle_fiber);

    /* set the idle fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_set_idle_fiber(sched, fib));

    /* POSTCONDITION: the idle fiber is set. */
    TEST_EXPECT(fib == ctx->idle_fiber);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
