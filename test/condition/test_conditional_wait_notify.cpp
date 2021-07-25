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
