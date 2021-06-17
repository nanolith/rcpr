/**
 * \file test/test_slist_append.cpp
 *
 * \brief Unit tests for slist_append.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/slist.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

TEST_SUITE(slist_append);

/**
 * Verify that we can append data to the end of an slist_node.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    slist* l = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an slist. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_create(
                &l, alloc));

    /* we should be able to get the head. */
    slist_node* head = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_head(&head, l));

    /* the head should be null. */
    TEST_ASSERT(nullptr == head);

    /* we should be able to get the tail. */
    slist_node* tail = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_tail(&tail, l));

    /* the tail should be null. */
    TEST_ASSERT(nullptr == tail);

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append_tail(l, allocator_resource_handle(r1)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == slist_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == slist_tail(&tail, l));

    /* they should both be equal and not null. */
    TEST_EXPECT(nullptr != head && head == tail);

    /* create a resource to append after this first resource. */
    allocator* r2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* append this after the head node. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append(head, allocator_resource_handle(r2)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == slist_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == slist_tail(&tail, l));

    /* they should not be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail);
    TEST_EXPECT(head != tail);

    /* get the resource for head. */
    resource* r1p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r1p, head));

    /* it should equal r1's resource handle. */
    TEST_EXPECT(r1p == allocator_resource_handle(r1));

    /* get the resource for tail. */
    resource* r2p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r2p, tail));

    /* it should equal r2's resource handle. */
    TEST_EXPECT(r2p == allocator_resource_handle(r2));

    /* create a resource to append after head. */
    allocator* r3 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* append this after the head node. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append(head, allocator_resource_handle(r3)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == slist_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == slist_tail(&tail, l));

    /* they should not be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail);
    TEST_EXPECT(head != tail);

    /* get the resource for head. */
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r1p, head));

    /* it should equal r1's resource handle. */
    TEST_EXPECT(r1p == allocator_resource_handle(r1));

    /* get the resource for tail. */
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r2p, tail));

    /* it should equal r2's resource handle. */
    TEST_EXPECT(r2p == allocator_resource_handle(r2));

    /* get the node after head. */
    slist_node* head_next = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_node_next(&head_next, head));

    /* get the resource for this node. */
    resource* r3p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r3p, head_next));

    /* it should equal the resource handle for r3. */
    TEST_EXPECT(r3p == allocator_resource_handle(r3));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(slist_resource_handle(l)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
