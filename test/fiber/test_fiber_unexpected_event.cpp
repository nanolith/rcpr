/**
 * \file test/fiber/test_fiber_unexpected_event.cpp
 *
 * \brief Unit tests for fiber_unexpected_event.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

TEST_SUITE(fiber_unexpected_event);

/**
 * Verify that when no handler has been set, an error is returned when calling
 * fiber_unexpected_event.
 */
TEST(no_handler)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* fib = nullptr;
    rcpr_uuid GOT_ID = { .data = {
        0x13, 0x6f, 0xa6, 0x76, 0xd3, 0x8b, 0x46, 0x68,
        0xac, 0x3e, 0x6f, 0x17, 0x34, 0x80, 0x43, 0xb4 } };
    rcpr_uuid EXPECTED_ID = { .data = {
        0x6a, 0x34, 0x55, 0x09, 0x79, 0x78, 0x41, 0xe5,
        0xbf, 0x03, 0x7f, 0xb2, 0x08, 0x5b, 0xb9, 0x36 } };

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
            disciplined_fiber_scheduler_main_fiber_get(&fib, sched));

    /* calling fiber_unexpected_event results in an error. */
    TEST_EXPECT(
        ERROR_FIBER_NO_UNEXPECTED_HANDLER ==
            fiber_unexpected_event(fib, &GOT_ID, 0, NULL, &EXPECTED_ID, 0));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

typedef struct unexpected_ctx unexpected_ctx;
struct unexpected_ctx
{
    bool called;
    fiber* fib;
    const rcpr_uuid* resume_disc_id;
    int resume_event;
    void* resume_param;
    const rcpr_uuid* expected_resume_disc_id;
    int expected_resume_event;
};

#define UNEXPECTED_HANDLER_RETURN_CODE -47

static status unexpected_handler(
    void* context, RCPR_SYM(fiber)* fib,
    const RCPR_SYM(rcpr_uuid)* resume_disc_id, int resume_event,
    void* resume_param, const RCPR_SYM(rcpr_uuid)* expected_resume_disc_id,
    int expected_resume_event)
{
    unexpected_ctx* ctx = (unexpected_ctx*)context;
    ctx->called = true;
    ctx->fib = fib;
    ctx->resume_disc_id = resume_disc_id;
    ctx->resume_event = resume_event;
    ctx->resume_param = resume_param;
    ctx->expected_resume_disc_id = expected_resume_disc_id;
    ctx->expected_resume_event = expected_resume_event;

    return UNEXPECTED_HANDLER_RETURN_CODE;
}

/**
 * Verify that all information is passed to the handler and back.
 */
TEST(handler)
{
    unexpected_ctx ctx;
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* fib = nullptr;
    rcpr_uuid GOT_ID = { .data = {
        0x13, 0x6f, 0xa6, 0x76, 0xd3, 0x8b, 0x46, 0x68,
        0xac, 0x3e, 0x6f, 0x17, 0x34, 0x80, 0x43, 0xb4 } };
    rcpr_uuid EXPECTED_ID = { .data = {
        0x6a, 0x34, 0x55, 0x09, 0x79, 0x78, 0x41, 0xe5,
        0xbf, 0x03, 0x7f, 0xb2, 0x08, 0x5b, 0xb9, 0x36 } };
    int EVENT_CODE = 1407;
    int EXPECTED_EVENT_CODE = 9009;
    void* EVENT_PARAM = (void*)alloc;

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
            disciplined_fiber_scheduler_main_fiber_get(&fib, sched));

    /* set the unexpected handler for the main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_unexpected_event_callback_add(
                fib, &unexpected_handler, &ctx));

    /* PRECONDITION: clear the context structure. */
    memset(&ctx, 0, sizeof(ctx));

    /* calling fiber_unexpected_event returns UNEXPECTED_HANDLER_RETURN_CODE. */
    TEST_EXPECT(
        UNEXPECTED_HANDLER_RETURN_CODE ==
            fiber_unexpected_event(
                fib, &GOT_ID, EVENT_CODE, EVENT_PARAM, &EXPECTED_ID,
                EXPECTED_EVENT_CODE));

    /* POSTCONDITION: the unexpected handler was called. */
    TEST_EXPECT(ctx.called);

    /* POSTCONDITION: the parameters were passed. */
    TEST_EXPECT(fib == ctx.fib);
    TEST_EXPECT(&GOT_ID == ctx.resume_disc_id);
    TEST_EXPECT(EVENT_CODE == ctx.resume_event);
    TEST_EXPECT(EVENT_PARAM == ctx.resume_param);
    TEST_EXPECT(&EXPECTED_ID == ctx.expected_resume_disc_id);
    TEST_EXPECT(EXPECTED_EVENT_CODE == ctx.expected_resume_event);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
