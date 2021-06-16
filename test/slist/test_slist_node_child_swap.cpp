/**
 * \file test/test_slist_node_child_swap.cpp
 *
 * \brief Unit tests for slist_node_child_swap.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/slist.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(slist_node_child_swap);

/**
 * Verify that we can swap the child resource in an slist_node.
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

    /* get the resource pointer. */
    resource* other_resource = allocator_resource_handle(other);

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append_tail(l, other_resource));

    /* get the head / tail. */
    TEST_ASSERT(STATUS_SUCCESS == slist_head(&head, l));

    /* get the resource associated with the head. */
    resource* r = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r, head));

    /* this resource should be the same as other. */
    TEST_EXPECT(r == allocator_resource_handle(other));

    /* create a resource to swap into the list. */
    allocator* newother = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&newother));

    /* save a copy of this resource. */
    resource* newother_resource = allocator_resource_handle(newother);
    resource* newother_resource_ref = newother_resource;

    /* swap the resources. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_node_child_swap(head, &newother_resource));

    /* now, newother should be the same as other. */
    TEST_EXPECT(newother_resource == other_resource);
    /* which is not the same as a copy of the original ref. */
    TEST_EXPECT(newother_resource != newother_resource_ref);

    /* if we get the resource, it will be the same as our previous newother. */
    TEST_ASSERT(STATUS_SUCCESS == slist_node_child(&r, head));
    TEST_EXPECT(r == newother_resource_ref);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(newother_resource));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(slist_resource_handle(l)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
