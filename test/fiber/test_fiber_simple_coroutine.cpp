/**
 * \file test/fiber/test_fiber_simple_coroutine.cpp
 *
 * \brief Simple coroutine example.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

using namespace std;

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

TEST_SUITE(fiber_simple_coroutine);

typedef struct test_fiber_scheduler_context test_fiber_scheduler_context;

#define CALL_COROUTINE 0x9215
#define RETURN_COROUTINE 0x9216

struct test_fiber_scheduler_context
{
    int calls;
    int yield_event1;
    fiber* main;
    fiber* coroutine;
    fiber* yield_fiber1;
    void* yield_param1;
};

struct test_coroutine_context
{
    int calls;
    fiber_scheduler* sched;
    fiber* coroutine;
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
        ctx->main = yield_fib;
        *resume_fib = yield_fib;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_MAIN;
        *resume_param = nullptr;

        return STATUS_SUCCESS;
    }
    else if (FIBER_SCHEDULER_YIELD_EVENT_ADD_FIBER == yield_event)
    {
        *resume_fib = yield_fib;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_ADD_FIBER;
        *resume_param = nullptr;
        ctx->coroutine = (fiber*)yield_param;

        return STATUS_SUCCESS;
    }
    else if (CALL_COROUTINE == yield_event)
    {
        *resume_fib = ctx->coroutine;
        *resume_event = CALL_COROUTINE;
        *resume_param = nullptr;

        return STATUS_SUCCESS;
    }
    else if (RETURN_COROUTINE == yield_event)
    {
        *resume_fib = ctx->main;
        *resume_event = RETURN_COROUTINE;
        *resume_param = yield_param;

        return STATUS_SUCCESS;
    }
    else if (FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE == yield_event)
    {
        *resume_fib = NULL;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_RESOURCE_RELEASE;
        *resume_param = nullptr;

        return resource_release(fiber_resource_handle(ctx->coroutine));
    }
    else
    {
        return -1;
    }
}

static status fiber_write_int(fiber_scheduler* sched, int64_t val)
{
    const rcpr_uuid* resume_id = nullptr;
    int resume_event = 0;
    void* resume_param = nullptr;

    return
        fiber_scheduler_yield(
            sched, RETURN_COROUTINE, (void*)val,
            &resume_id, &resume_event, &resume_param);
}

static status fiber_read_int(fiber_scheduler* sched, int64_t* val)
{
    status retval;
    const rcpr_uuid* resume_id = nullptr;
    int resume_event = 0;
    void* resume_param = nullptr;

    retval =
        fiber_scheduler_yield(
            sched, CALL_COROUTINE, nullptr,
            &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS == retval)
    {
        *val = (int64_t)resume_param;
    }

    return retval;
}

static status coroutine_fn(void* context)
{
    status retval;
    test_coroutine_context* ctx = (test_coroutine_context*)context;

    for (int i = 0; i < 10; ++i)
    {
        retval = fiber_write_int(ctx->sched, i);
        if (STATUS_SUCCESS != retval)
            return retval;
    }

    return STATUS_SUCCESS;
}

/**
 * Verify that we can yield to the scheduler.
 */
TEST(coroutine)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* coroutine = nullptr;
    test_fiber_scheduler_context ctx;
    test_coroutine_context coroutine_ctx;

    /* clear the test fiber scheduler context. */
    memset(&ctx, 0, sizeof(ctx));

    /* clear the test coroutine context. */
    memset(&coroutine_ctx, 0, sizeof(coroutine_ctx));

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

    /* we should be able to create a coroutine fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &coroutine, alloc, sched, 16384, &coroutine_ctx,
                &coroutine_fn));

    /* set coroutine context values. */
    coroutine_ctx.coroutine = coroutine;
    coroutine_ctx.sched = sched;

    /* add the fiber to the scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_add(sched, coroutine));

    /* call the coroutine 10 times. */
    for (int i = 0; i < 10; ++i)
    {
        int64_t val;
        TEST_ASSERT(
            STATUS_SUCCESS ==
                fiber_read_int(sched, &val));

        TEST_ASSERT(val == i);
    }

    /* we should be able to release the fiber scheduler instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
