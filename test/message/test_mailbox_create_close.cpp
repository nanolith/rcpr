/**
 * \file test/message/test_mailbox_create_close.cpp
 *
 * \brief Unit tests for mailbox_create and mailbox_close.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/message.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_resource;

TEST_SUITE(mailbox_create_close);

/**
 * Verify that we can create a mailbox instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* msgdisc = nullptr;
    mailbox_address addr = -1;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the message discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_discipline_get_or_create(&msgdisc, alloc, sched));

    /* we should be able to create a mailbox. */
    TEST_EXPECT(
        STATUS_SUCCESS ==
            mailbox_create(&addr, msgdisc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can close a mailbox instance.
 */
TEST(close)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* msgdisc = nullptr;
    mailbox_address addr = -1;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the message discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_discipline_get_or_create(&msgdisc, alloc, sched));

    /* we should be able to create a mailbox. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            mailbox_create(&addr, msgdisc));

    /* we should be able to close a mailbox. */
    TEST_EXPECT(
        STATUS_SUCCESS ==
            mailbox_close(addr, msgdisc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}
