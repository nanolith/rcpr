/**
 * \file test/message/test_conditional_wait_notify.cpp
 *
 * \brief Unit tests for conditional_wait, conditional_notify_one, and
 * conditional_notify_all.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/condition.h>
#include <string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_condition;
RCPR_IMPORT_resource;

TEST_SUITE(conditional_wait_notify);

#define TEST_FIBER_STATE_NOT_STARTED 0
#define TEST_FIBER_STATE_STARTED 1
#define TEST_FIBER_STATE_FINISHED 2
#define TEST_FIBER_STATE_ERROR 3

typedef struct test_fiber_context test_fiber_context;
struct test_fiber_context
{
    int state;
    conditional cond;
    fiber_scheduler_discipline* condisc;
};

static status test_fiber_entry(void* context)
{
    test_fiber_context* ctx = (test_fiber_context*)context;

    /* set the fiber state to started. */
    ctx->state = TEST_FIBER_STATE_STARTED;

    /* wait to be notified. */
    status retval = conditional_wait(ctx->cond, ctx->condisc);
    if (STATUS_SUCCESS != retval)
    {
        ctx->state = TEST_FIBER_STATE_ERROR;
        return retval;
    }

    /* set the fiber state to finished. */
    ctx->state = TEST_FIBER_STATE_FINISHED;

    return STATUS_SUCCESS;
}

/**
 * Verify that a fiber that calls conditional_wait is suspended.
 */
TEST(wait)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* condisc = nullptr;
    fiber* fib = nullptr;
    conditional cond = -1;
    test_fiber_context ctx;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the condition discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            condition_discipline_get_or_create(&condisc, alloc, sched));

    /* we should be able to create a conditional. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_create(&cond, condisc));

    /* clear the test context. */
    memset(&ctx, 0, sizeof(test_fiber_context));

    /* set context values. */
    ctx.cond = cond;
    ctx.condisc = condisc;

    /* we should be able to create a fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &fib, alloc, sched, 16384, &ctx, &test_fiber_entry));

    /* we should be able to add this fiber to the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, fib));

    /* precondition: the context state should be NOT_STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_NOT_STARTED == ctx.state);

    /* run the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_run(sched));

    /* postcondition: the context state should be STARTED. */
    TEST_EXPECT(TEST_FIBER_STATE_STARTED == ctx.state);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that a waiting fiber can be restarted by calling notify_one.
 */
TEST(notify_one)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* condisc = nullptr;
    fiber* fib = nullptr;
    conditional cond = -1;
    test_fiber_context ctx;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the condition discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            condition_discipline_get_or_create(&condisc, alloc, sched));

    /* we should be able to create a conditional. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_create(&cond, condisc));

    /* clear the test context. */
    memset(&ctx, 0, sizeof(test_fiber_context));

    /* set context values. */
    ctx.cond = cond;
    ctx.condisc = condisc;

    /* we should be able to create a fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &fib, alloc, sched, 16384, &ctx, &test_fiber_entry));

    /* we should be able to add this fiber to the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, fib));

    /* run the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_run(sched));

    /* precondition: the context state should be STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_STARTED == ctx.state);

    /* notify one fiber to start. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_notify_one(cond, condisc));

    /* postcondition: the context state should be FINISHED. */
    TEST_ASSERT(TEST_FIBER_STATE_FINISHED == ctx.state);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that all waiting fibers can be restarted one at a time by calling
 * notify_one.
 */
TEST(notify_one_multiple)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* condisc = nullptr;
    fiber* fib1 = nullptr;
    fiber* fib2 = nullptr;
    conditional cond = -1;
    test_fiber_context ctx1;
    test_fiber_context ctx2;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the condition discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            condition_discipline_get_or_create(&condisc, alloc, sched));

    /* we should be able to create a conditional. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_create(&cond, condisc));

    /* clear the first test context. */
    memset(&ctx1, 0, sizeof(test_fiber_context));

    /* clear the second test context. */
    memset(&ctx2, 0, sizeof(test_fiber_context));

    /* set first context values. */
    ctx1.cond = cond;
    ctx1.condisc = condisc;

    /* set second context values. */
    ctx2.cond = cond;
    ctx2.condisc = condisc;

    /* we should be able to create the first fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &fib1, alloc, sched, 16384, &ctx1, &test_fiber_entry));

    /* we should be able to create the second fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &fib2, alloc, sched, 16384, &ctx2, &test_fiber_entry));

    /* we should be able to add the first fiber to the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, fib1));

    /* we should be able to add the second fiber to the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, fib2));

    /* run the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_run(sched));

    /* precondition: the first context state should be STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_STARTED == ctx1.state);

    /* precondition: the second context state should be STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_STARTED == ctx2.state);

    /* notify one fiber to start. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_notify_one(cond, condisc));

    /* postcondition: the first context state should be FINISHED. */
    TEST_ASSERT(TEST_FIBER_STATE_FINISHED == ctx1.state);

    /* precondition: the second context state is still STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_STARTED == ctx2.state);

    /* notify one fiber to start. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_notify_one(cond, condisc));

    /* postcondition: the second context state should be FINISHED. */
    TEST_ASSERT(TEST_FIBER_STATE_FINISHED == ctx2.state);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that all waiting fibers can be restarted at once by calling
 * notify_all.
 */
TEST(notify_all)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* condisc = nullptr;
    fiber* fib1 = nullptr;
    fiber* fib2 = nullptr;
    conditional cond = -1;
    test_fiber_context ctx1;
    test_fiber_context ctx2;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the condition discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            condition_discipline_get_or_create(&condisc, alloc, sched));

    /* we should be able to create a conditional. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_create(&cond, condisc));

    /* clear the first test context. */
    memset(&ctx1, 0, sizeof(test_fiber_context));

    /* clear the second test context. */
    memset(&ctx2, 0, sizeof(test_fiber_context));

    /* set first context values. */
    ctx1.cond = cond;
    ctx1.condisc = condisc;

    /* set second context values. */
    ctx2.cond = cond;
    ctx2.condisc = condisc;

    /* we should be able to create the first fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &fib1, alloc, sched, 16384, &ctx1, &test_fiber_entry));

    /* we should be able to create the second fiber instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &fib2, alloc, sched, 16384, &ctx2, &test_fiber_entry));

    /* we should be able to add the first fiber to the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, fib1));

    /* we should be able to add the second fiber to the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, fib2));

    /* run the scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_run(sched));

    /* precondition: the first context state should be STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_STARTED == ctx1.state);

    /* precondition: the second context state should be STARTED. */
    TEST_ASSERT(TEST_FIBER_STATE_STARTED == ctx2.state);

    /* notify all fibers to start. */
    TEST_ASSERT(STATUS_SUCCESS == conditional_notify_all(cond, condisc));

    /* postcondition: the first context state should be FINISHED. */
    TEST_ASSERT(TEST_FIBER_STATE_FINISHED == ctx1.state);

    /* postcondition: the second context state should be FINISHED. */
    TEST_ASSERT(TEST_FIBER_STATE_FINISHED == ctx2.state);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}
