/**
 * \file test/list/test_list_count.cpp
 *
 * \brief Unit tests for list_count.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/list.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(list_count);

/**
 * Verify that we can count the number of nodes in a list.
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

    /* the initial count should be 0. */
    TEST_EXPECT(0 == list_count(l));

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(r1)));

    /* the new count should be 1. */
    TEST_EXPECT(1 == list_count(l));

    /* create a resource to insert into the list. */
    allocator* r2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(r2)));

    /* the new count should be 2. */
    TEST_EXPECT(2 == list_count(l));

    /* create a resource to insert into the list. */
    allocator* r3 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            list_append_tail(l, allocator_resource_handle(r3)));

    /* the new count should be 3. */
    TEST_EXPECT(3 == list_count(l));

    /* we should be able to release the list instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(list_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
