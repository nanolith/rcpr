/**
 * \file test/test_slist_create.cpp
 *
 * \brief Unit tests for slist_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/slist.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

TEST_SUITE(slist_create);

/**
 * Verify that we can create and release an slist instance.
 */
TEST(create)
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

    /* we should be able to release the slist instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(slist_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
