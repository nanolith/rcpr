/**
 * \file test/test_list_insert_head.cpp
 *
 * \brief Unit tests for list_insert_head.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/list.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

TEST_SUITE(list_insert_head);

/**
 * Verify that we can insert data into list instance.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    list* l = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

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
    allocator* other = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_insert_head(l, allocator_resource_handle(other)));

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

    /* get the next for tail. */
    list_node* tail_next = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == list_node_next(&tail_next, tail));

    /* tail->next should be null. */
    TEST_ASSERT(nullptr == tail_next);

    /* we should be able to release the list instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(list_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can insert two values into the list, and that the second value
 * becomes the new head.
 */
TEST(double_insert)
{
    allocator* alloc = nullptr;
    list* l = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

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

    /* create the first resource to insert into the list. */
    allocator* other1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_insert_head(l, allocator_resource_handle(other1)));

    /* create the second resource to insert into the list. */
    allocator* other2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other2));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_insert_head(l, allocator_resource_handle(other2)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&tail, l));

    /* The head and tail should exist, and they should NOT be equal. */
    TEST_EXPECT(nullptr != head && nullptr != tail && head != tail);

    /* get the resource associated with the head. */
    resource* r1 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r1, head));

    /* this resource should be the same as other2. */
    TEST_EXPECT(r1 == allocator_resource_handle(other2));

    /* get the resource associated with the tail. */
    resource* r2 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r2, tail));

    /* this resource should be the same as other1. */
    TEST_EXPECT(r2 == allocator_resource_handle(other1));

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

    /* head->prev should be NULL. */
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
