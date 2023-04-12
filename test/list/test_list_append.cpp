/**
 * \file test/test_list_append.cpp
 *
 * \brief Unit tests for list_append.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/list.h>

#include "../mock_allocator/mock_allocator.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_mock_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(list_append);

/**
 * Verify that we can append data to the end of a list_node.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    list* l = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_create(
                &l, alloc));

    /* we should be able to get the head. */
    list_node* head = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_head(&head, l));

    /* the head should be null. */
    TEST_ASSERT(nullptr == head);

    /* we should be able to get the tail. */
    list_node* tail = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_tail(&tail, l));

    /* the tail should be null. */
    TEST_ASSERT(nullptr == tail);

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(r1)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should both be equal and not null. */
    TEST_EXPECT(nullptr != head && head == tail);

    /* create a resource to append after this first resource. */
    allocator* r2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* append this after the head node. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append(head, allocator_resource_handle(r2)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should not be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail);
    TEST_EXPECT(head != tail);

    /* get the resource for head. */
    resource* r1p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r1p, head));

    /* it should equal r1's resource handle. */
    TEST_EXPECT(r1p == allocator_resource_handle(r1));

    /* get the resource for tail. */
    resource* r2p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r2p, tail));

    /* it should equal r2's resource handle. */
    TEST_EXPECT(r2p == allocator_resource_handle(r2));

    /* create a resource to append after head. */
    allocator* r3 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* append this after the head node. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append(head, allocator_resource_handle(r3)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should not be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail);
    TEST_EXPECT(head != tail);

    /* get the resource for head. */
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r1p, head));

    /* it should equal r1's resource handle. */
    TEST_EXPECT(r1p == allocator_resource_handle(r1));

    /* get the resource for tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r2p, tail));

    /* it should equal r2's resource handle. */
    TEST_EXPECT(r2p == allocator_resource_handle(r2));

    /* get the node after head. */
    list_node* head_next = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_next(&head_next, head));

    /* get the resource for this node. */
    resource* r3p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r3p, head_next));

    /* it should equal the resource handle for r3. */
    TEST_EXPECT(r3p == allocator_resource_handle(r3));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(list_resource_handle(l)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that when allocation fails during a list_append_tail, an error is
 * returned.
 */
TEST(allocation_fail_list_append_tail)
{
    allocator* alloc = nullptr;
    list* l = nullptr;

    /* we should be able to create a mock allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == mock_allocator_create(&alloc));

    /* we should be able to create a list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_create(
                &l, alloc));

    /* we should be able to get the head. */
    list_node* head = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_head(&head, l));

    /* the head should be null. */
    TEST_ASSERT(nullptr == head);

    /* we should be able to get the tail. */
    list_node* tail = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_tail(&tail, l));

    /* the tail should be null. */
    TEST_ASSERT(nullptr == tail);

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* make the allocator return an out-of-memory error. */
    mock_allocator_allocate_status_code_set(alloc, ERROR_GENERAL_OUT_OF_MEMORY);

    /* inserting this into the list will now fail. */
    TEST_ASSERT(
        ERROR_GENERAL_OUT_OF_MEMORY ==
            list_append_tail(l, allocator_resource_handle(r1)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should both be NULL. */
    TEST_EXPECT(nullptr == head && head == tail);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(r1)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(list_resource_handle(l)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that when allocation fails during a list_append, an error is returned.
 */
TEST(allocation_fail_list_append)
{
    allocator* alloc = nullptr;
    list* l = nullptr;

    /* we should be able to create a mock allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == mock_allocator_create(&alloc));

    /* we should be able to create a list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_create(
                &l, alloc));

    /* we should be able to get the head. */
    list_node* head = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_head(&head, l));

    /* the head should be null. */
    TEST_ASSERT(nullptr == head);

    /* we should be able to get the tail. */
    list_node* tail = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_tail(&tail, l));

    /* the tail should be null. */
    TEST_ASSERT(nullptr == tail);

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(r1)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should both be equal and not null. */
    TEST_EXPECT(nullptr != head && head == tail);

    /* create a resource to append after this first resource. */
    allocator* r2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* make the allocator return an out-of-memory error. */
    mock_allocator_allocate_status_code_set(alloc, ERROR_GENERAL_OUT_OF_MEMORY);

    /* appending this after the head node should fail. */
    TEST_ASSERT(
        ERROR_GENERAL_OUT_OF_MEMORY ==
            list_append(head, allocator_resource_handle(r2)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should both be equal and not null. */
    TEST_EXPECT(nullptr != head && head == tail);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(r2)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(list_resource_handle(l)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
