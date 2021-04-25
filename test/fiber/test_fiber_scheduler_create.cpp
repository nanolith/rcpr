/**
 * \file test/fiber/test_fiber_scheduler_create.cpp
 *
 * \brief Unit tests for fiber_scheduler_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

TEST_SUITE(fiber_scheduler_create);

typedef struct test_fiber_scheduler_context test_fiber_scheduler_context;

struct test_fiber_scheduler_context
{
    int calls;
    int yield_event1;
    fiber* yield_fiber1;
    void* yield_param1;
};

static status test_fiber_scheduler_callback(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, const rcpr_uuid** resume_id, int* resume_event,
    void** resume_param)
{
    test_fiber_scheduler_context* ctx = (test_fiber_scheduler_context*)context;

    if (0 == ctx->calls)
    {
        ctx->yield_event1 = yield_event;
        ctx->yield_fiber1 = yield_fib;
        ctx->yield_param1 = yield_param;
    }

    /* increment the number of calls. */
    ++ctx->calls;

    /* is this a main fiber add? */
    if (FIBER_SCHEDULER_YIELD_EVENT_MAIN == yield_event)
    {
        *resume_fib = yield_fib;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_MAIN;
        *resume_param = nullptr;

        return STATUS_SUCCESS;
    }
    else if (FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE == yield_event)
    {
        *resume_fib = NULL;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_RESOURCE_RELEASE;
        *resume_param = nullptr;

        return STATUS_SUCCESS;
    }
    else
    {
        return -1;
    }
}

/**
 * Verify that we can create a fiber scheduler instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    test_fiber_scheduler_context ctx;

    /* clear the test fiber scheduler context. */
    memset(&ctx, 0, sizeof(ctx));

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* PRECONDITIONS: calls is 0. */
    TEST_ASSERT(0 == ctx.calls);

    /* we should be able to create a fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create(
                &sched, alloc, &ctx, &test_fiber_scheduler_callback));

    /* POSTCONDITIONS: one call was made to cache the main fiber. */
    TEST_EXPECT(1 == ctx.calls);
    TEST_EXPECT(nullptr != ctx.yield_fiber1);
    TEST_EXPECT(FIBER_SCHEDULER_YIELD_EVENT_MAIN == ctx.yield_event1);
    TEST_EXPECT(nullptr == ctx.yield_param1);

    /* Release PRECONDITIONS: zero out the calls. */
    ctx.calls = 0;

    /* we should be able to release the fiber scheduler instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));

    /* the scheduler should have been called. */
    TEST_EXPECT(1 == ctx.calls);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
