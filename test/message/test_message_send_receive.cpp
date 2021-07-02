/**
 * \file test/message/test_message_send.cpp
 *
 * \brief Unit tests for message_send and message_receive.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/message.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_resource;

/**
 * Verify that we can send a message to a mailbox.
 */
TEST(message_send)
{
    allocator* alloc = nullptr;
    allocator* payload_allocator;
    resource* payload = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* msgdisc = nullptr;
    mailbox_address addr = -1;
    message* msg = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a dummy allocator for our payload. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&payload_allocator));

    /* convert the payload allocator to a resource. */
    payload = allocator_resource_handle(payload_allocator);

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

    /* we should be able to create a message. */
    TEST_ASSERT(
        STATUS_SUCCESS == message_create(&msg, alloc, addr, payload));

    /* we should be able to send a message to this mailbox. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_send(addr, msg, msgdisc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can receive a message sent to a mailbox.
 */
TEST(message_receive)
{
    allocator* alloc = nullptr;
    allocator* payload_allocator;
    resource* payload = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* msgdisc = nullptr;
    mailbox_address addr = -1;
    message* msg = nullptr;
    message* recvmsg = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a dummy allocator for our payload. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&payload_allocator));

    /* convert the payload allocator to a resource. */
    payload = allocator_resource_handle(payload_allocator);

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

    /* we should be able to create a message. */
    TEST_ASSERT(
        STATUS_SUCCESS == message_create(&msg, alloc, addr, payload));

    /* we should be able to send a message to this mailbox. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_send(addr, msg, msgdisc));

    /* we should be able to receive a message from this mailbox. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_receive(addr, &recvmsg, msgdisc));

    /* the two message pointers should match. */
    TEST_EXPECT(msg == recvmsg);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}
