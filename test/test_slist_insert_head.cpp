/**
 * \file test/test_slist_insert_head.cpp
 *
 * \brief Unit tests for slist_insert_head.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/slist.h>

TEST_SUITE(slist_insert_head);

/**
 * Verify that we can insert data into an slist instance.
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
    allocator* other = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&other));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_insert_head(l, allocator_resource_handle(other)));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == slist_head(&head, l));
    TEST_ASSERT(STATUS_SUCCESS == slist_tail(&tail, l));

    /* they should both be equal and not null. */
    TEST_EXPECT(nullptr != head && head == tail);

    /* get the resource associated with the head. */
    resource* r = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r, head));

    /* this resource should be the same as other. */
    TEST_EXPECT(r == allocator_resource_handle(other));

    /* we should be able to release the slist instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(slist_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
