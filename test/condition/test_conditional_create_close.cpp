/**
 * \file test/message/test_conditional_create_close.cpp
 *
 * \brief Unit tests for conditional_create and conditional_close.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/condition.h>

#ifdef RCPR_FIBER_FOUND

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_condition;
RCPR_IMPORT_resource;

TEST_SUITE(conditional_create_close);

/**
 * Verify that we can create a conditional instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* condisc = nullptr;
    conditional cond = -1;

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
    TEST_EXPECT(STATUS_SUCCESS == conditional_create(&cond, condisc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can create and close a conditional instance.
 */
TEST(create_and_close)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* condisc = nullptr;
    conditional cond = -1;

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

    /* we should be able to close a conditional. */
    TEST_EXPECT(STATUS_SUCCESS == conditional_close(cond, condisc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

#endif /* RCPR_FIBER_FOUND */
