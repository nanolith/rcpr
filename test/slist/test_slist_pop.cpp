/**
 * \file test/test_slist_pop.cpp
 *
 * \brief Unit tests for slist_pop.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/slist.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

TEST_SUITE(slist_pop);

/**
 * Verify that we can pop data inserted into an slist instance.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    slist* l = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an slist. */
    TEST_ASSERT(STATUS_SUCCESS == slist_create(&l, alloc));

    /* create a resource to insert into the list. */
    allocator* r1 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_insert_head(l, allocator_resource_handle(r1)));

    /* create another resource to insert into the list. */
    allocator* r2 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* insert this into the list. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            slist_insert_head(l, allocator_resource_handle(r2)));

    /* pop the second resource off of the list. */
    resource* r2p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_pop(l, &r2p));

    /* pop the first resource off of the list. */
    resource* r1p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == slist_pop(l, &r1p));

    /* verify that these resource pointers match our allocators. */
    TEST_ASSERT(r1p == allocator_resource_handle(r1));
    TEST_ASSERT(r2p == allocator_resource_handle(r2));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(slist_resource_handle(l)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(r1p));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(r2p));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}
