/**
 * \file test/fiber/test_disciplined_fiber_scheduler_set_next_fiber_to_run.cpp
 *
 * \brief Unit tests for disciplined_fiber_scheduler_set_next_fiber_to_run.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

#include "../../src/fiber/common/fiber_internal.h"

TEST_SUITE(disciplined_fiber_scheduler_set_next_fiber_to_run);

/**
 * Verify that we can add a fiber to the run queue.
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

    /* we should be able to create a dummy thread fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create_for_thread(&fib, alloc));

    /* PRECONDITION: the run queue is empty. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;
    TEST_ASSERT(
        0 == queue_count(ctx->run_queue));

    /* PRECONDITION: set dummy resume values. */
    fib->restore_discipline_id = nullptr;
    fib->restore_reason_code = 0;
    fib->restore_param = nullptr;

    /* we should be able to add a fiber to the run queue. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_set_next_fiber_to_run(
                sched, fib, &id, 1, alloc));

    /* POSTCONDITION: the run queue has one item. */
    TEST_EXPECT(
        1 == queue_count(ctx->run_queue));

    /* POSTCONDITION: the dummy resume values are set. */
    TEST_EXPECT(&id == fib->restore_discipline_id);
    TEST_EXPECT(1 == fib->restore_reason_code);
    TEST_EXPECT(alloc == fib->restore_param);
    
    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_resource_handle(fib)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
