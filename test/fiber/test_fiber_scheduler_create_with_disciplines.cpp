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
    fiber** resume_fib, int* resume_event, void** resume_param)
{
    test_fiber_scheduler_context* ctx = (test_fiber_scheduler_context*)context;

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
