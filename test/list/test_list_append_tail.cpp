/**
 * \file test/test_list_append_tail.cpp
 *
 * \brief Unit tests for list_append_tail.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/list.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(list_append_tail);

/**
 * Verify that we can append data to an list instance.
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
    allocator* other = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(other)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* they should both be equal and not null. */
    TEST_EXPECT(nullptr != head && head == tail);

    /* get the resource associated with the head. */
    resource* r = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r, head));

    /* this resource should be the same as other. */
    TEST_EXPECT(r == allocator_resource_handle(other));

    /* get the next for head. */
    list_node* head_next = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_next(&head_next, head));

    /* head->next should be null. */
    TEST_ASSERT(nullptr == head_next);

    /* get the prev for head. */
    list_node* head_prev = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_prev(&head_prev, head));

    /* head->prev should be null. */
    TEST_ASSERT(nullptr == head_prev);

    /* get the next for tail. */
    list_node* tail_next = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_next(&tail_next, tail));

    /* tail->next should be null. */
    TEST_ASSERT(nullptr == tail_next);

    /* get the prev for tail. */
    list_node* tail_prev = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_prev(&tail_prev, tail));

    /* tail->prev should be null. */
    TEST_ASSERT(nullptr == tail_prev);

    /* we should be able to release the list instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(list_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can append two values to the list, and that the second value
 * becomes the new tail.
 */
TEST(double_append)
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

    /* create the first resource to insert into the list. */
    allocator* other1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other1));

    /* append this to the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(other1)));

    /* create the second resource to insert into the list. */
    allocator* other2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other2));

    /* append this to the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(other2)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* The head and tail should exist, and they should NOT be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail && head != tail);

    /* get the resource associated with the head. */
    resource* r1 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r1, head));

    /* this resource should be the same as other1. */
    TEST_EXPECT(r1 == allocator_resource_handle(other1));

    /* get the resource associated with the tail. */
    resource* r2 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r2, tail));

    /* this resource should be the same as other2. */
    TEST_EXPECT(r2 == allocator_resource_handle(other2));

    /* get the next for head. */
    list_node* head_next = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_next(&head_next, head));

    /* head->next should be tail. */
    TEST_ASSERT(tail == head_next);

    /* get the prev for head. */
    list_node* head_prev = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_prev(&head_prev, head));

    /* head->prev should be null. */
    TEST_ASSERT(nullptr == head_prev);

    /* get the next for tail. */
    list_node* tail_next = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_next(&tail_next, tail));

    /* tail->next should be null. */
    TEST_ASSERT(nullptr == tail_next);

    /* get the prev for tail. */
    list_node* tail_prev = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_prev(&tail_prev, tail));

    /* tail->prev should be head. */
    TEST_ASSERT(head == tail_prev);

    /* we should be able to release the list instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(list_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
