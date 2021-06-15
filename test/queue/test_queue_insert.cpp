/**
 * \file test/test_queue_insert.cpp
 *
 * \brief Unit tests for queue_insert.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/queue.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(queue_insert);

/**
 * Verify that we can insert resources to a queue instance.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    queue* q = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_create( &q, alloc));

    /* the count for the queue should be 0. */
    TEST_EXPECT(0 == queue_count(q));

    /* create a dummy resource. */
    allocator* r1 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r1));

    /* get the handle for this resource. */
    resource* r1h = allocator_resource_handle(r1);

    /* insert this resource to the queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_insert(q, r1h));

    /* the count for the queue should be 1. */
    TEST_EXPECT(1 == queue_count(q));

    /* create a dummy resource. */
    allocator* r2 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* get the handle for this resource. */
    resource* r2h = allocator_resource_handle(r2);

    /* insert this resource to the queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_insert(q, r2h));

    /* the count for the queue should be 2. */
    TEST_EXPECT(2 == queue_count(q));

    /* create a dummy resource. */
    allocator* r3 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* get the handle for this resource. */
    resource* r3h = allocator_resource_handle(r3);

    /* insert this resource to the queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_insert(q, r3h));

    /* the count for the queue should be 3. */
    TEST_EXPECT(3 == queue_count(q));

    /* pop the third resource from the front of the queue. */
    resource* p3 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == queue_pop(q, &p3));

    /* this should be the same as our third resource. */
    TEST_ASSERT(r3h == p3);

    /* release this resource. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(p3));

    /* the count for the queue should be 2. */
    TEST_EXPECT(2 == queue_count(q));

    /* pop the second resource from the front of the queue. */
    resource* p2 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == queue_pop(q, &p2));

    /* this should be the same as our second resource. */
    TEST_ASSERT(r2h == p2);

    /* release this resource. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(p2));

    /* the count for the queue should be 1. */
    TEST_EXPECT(1 == queue_count(q));

    /* pop the first resource from the front of the queue. */
    resource* p1 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == queue_pop(q, &p1));

    /* this should be the same as our first resource. */
    TEST_ASSERT(r1h == p1);

    /* release this resource. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(p1));

    /* the count for the queue should be 0. */
    TEST_EXPECT(0 == queue_count(q));

    /* we should be able to release the queue instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(queue_resource_handle(q)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
