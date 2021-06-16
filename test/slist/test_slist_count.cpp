/**
 * \file test/test_slist_count.cpp
 *
 * \brief Unit tests for slist_count.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/slist.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(slist_count);

/**
 * Verify that we can count the number of nodes in an slist.
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

    /* the initial count should be 0. */
    TEST_EXPECT(0 == slist_count(l));

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append_tail(l, allocator_resource_handle(r1)));

    /* the new count should be 1. */
    TEST_EXPECT(1 == slist_count(l));

    /* create a resource to insert into the list. */
    allocator* r2 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append_tail(l, allocator_resource_handle(r2)));

    /* the new count should be 2. */
    TEST_EXPECT(2 == slist_count(l));

    /* create a resource to insert into the list. */
    allocator* r3 = nullptr;
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_append_tail(l, allocator_resource_handle(r3)));

    /* the new count should be 3. */
    TEST_EXPECT(3 == slist_count(l));

    /* we should be able to release the slist instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(slist_resource_handle(l)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
