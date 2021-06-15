/**
 * \file test/message/test_message_create.cpp
 *
 * \brief Unit tests for message_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/message.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(message_create);

/**
 * Verify that we can create and release a message instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    message* msg = nullptr;
    allocator* payload_allocator = nullptr;
    resource* payload = nullptr;
    mailbox_address returnaddr = 907;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a dummy allocator for our payload. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* convert the payload allocator to a resource. */
    payload = allocator_resource_handle(payload_allocator);

    /* we should be able to create a message. */
    TEST_ASSERT(
        STATUS_SUCCESS == message_create(&msg, alloc, returnaddr, payload));

    /* the return address matches. */
    TEST_EXPECT(
        returnaddr == message_return_address(msg));

    /* the payload matches. */
    TEST_EXPECT(
        payload == message_payload(msg, false));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(message_resource_handle(msg)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
