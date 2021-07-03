/**
 * \file test/fiber/test_disciplined_fiber_scheduler_remove_fiber.cpp
 *
 * \brief Unit tests for disciplined_fiber_scheduler_remove_fiber.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

#include "../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

TEST_SUITE(disciplined_fiber_scheduler_remove_fiber);

/**
 * Verify that we can remove a fiber from the disciplined scheduler.
 */
TEST(remove)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* fib = nullptr;
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
            fiber_create_for_thread(&fib, sched, alloc));

    /* PRECONDITION: the fiber is in the fiber rbtree. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;
    resource* found_resource = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_insert(ctx->fibers_by_pointer, fiber_resource_handle(fib)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_find(&found_resource, ctx->fibers_by_pointer, fib));

    /* we should be able to remove the fiber from the tree. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_remove_fiber(
                sched, fib));

    /* POSTCONDITION: the fiber tree no longer has this fiber. */
    TEST_EXPECT(
        ERROR_RBTREE_NOT_FOUND ==
            rbtree_find(&found_resource, ctx->fibers_by_pointer, fib));

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
