/**
 * \file test/test_list_insert.cpp
 *
 * \brief Unit tests for list_insert.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/list.h>

TEST_SUITE(list_insert);

/**
 * Verify that we can insert data before a list node.
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

    /* create a resource to insert before this first resource. */
    allocator* r2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* insert this before the head node. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_insert(head, allocator_resource_handle(r2)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should not be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail);
    TEST_EXPECT(head != tail);

    /* get the resource for head. */
    resource* r1p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r1p, head));

    /* it should equal r2's resource handle. */
    TEST_EXPECT(r1p == allocator_resource_handle(r2));

    /* get the resource for tail. */
    resource* r2p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r2p, tail));

    /* it should equal r1's resource handle. */
    TEST_EXPECT(r2p == allocator_resource_handle(r1));

    /* create a resource to insert after tail. */
    allocator* r3 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* insert this before the tail node. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_insert(tail, allocator_resource_handle(r3)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should not be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail);
    TEST_EXPECT(head != tail);

    /* get the resource for head. */
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r1p, head));

    /* it should equal r2's resource handle. */
    TEST_EXPECT(r1p == allocator_resource_handle(r2));

    /* get the resource for tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r2p, tail));

    /* it should equal r1's resource handle. */
    TEST_EXPECT(r2p == allocator_resource_handle(r1));

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
