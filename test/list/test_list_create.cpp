/**
 * \file test/test_list_create.cpp
 *
 * \brief Unit tests for list_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/list.h>

#include "../mock_allocator/mock_allocator.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_mock_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(list_create);

/**
 * Verify that we can create and release a list instance.
 */
TEST(create)
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

    /* we should be able to release the list instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(list_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that if allocation fails, then list_create fails.
 */
TEST(allocation_fail)
{
    allocator* alloc = nullptr;
    list* l = nullptr;

    /* we should be able to create a mock allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == mock_allocator_create(&alloc));

    /* make the allocator return an out-of-memory error. */
    mock_allocator_allocate_status_code_set(alloc, ERROR_GENERAL_OUT_OF_MEMORY);

    /* creating the list should fail. */
    TEST_ASSERT(
        ERROR_GENERAL_OUT_OF_MEMORY ==
            list_create(
                &l, alloc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
