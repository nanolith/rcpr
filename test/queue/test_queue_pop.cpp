/**
 * \file test/test_queue_pop.cpp
 *
 * \brief Unit tests for queue_pop.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/queue.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_queue;
RCPR_IMPORT_resource;

TEST_SUITE(queue_pop);

/**
 * Verify that we can pop resources off of the head of a queue instance.
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

    /* append this resource to the queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_append(q, r1h));

    /* the count for the queue should be 1. */
    TEST_EXPECT(1 == queue_count(q));

    /* create a dummy resource. */
    allocator* r2 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r2));

    /* get the handle for this resource. */
    resource* r2h = allocator_resource_handle(r2);

    /* append this resource to the queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_append(q, r2h));

    /* the count for the queue should be 2. */
    TEST_EXPECT(2 == queue_count(q));

    /* create a dummy resource. */
    allocator* r3 = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&r3));

    /* get the handle for this resource. */
    resource* r3h = allocator_resource_handle(r3);

    /* append this resource to the queue. */
    TEST_ASSERT(STATUS_SUCCESS == queue_append(q, r3h));

    /* the count for the queue should be 3. */
    TEST_EXPECT(3 == queue_count(q));

    /* popping the first element yields the first resource. */
    resource* r1p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == queue_pop(q, &r1p));
    TEST_ASSERT(NULL != r1p);

    /* this is the first resource. */
    TEST_EXPECT(r1p == r1h);

    /* the count for the queue should be 2. */
    TEST_EXPECT(2 == queue_count(q));

    /* popping the next element yields the second resource. */
    resource* r2p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == queue_pop(q, &r2p));
    TEST_ASSERT(NULL != r2p);

    /* this is the second resource. */
    TEST_EXPECT(r2p == r2h);

    /* the count for the queue should be 1. */
    TEST_EXPECT(1 == queue_count(q));

    /* popping the last element yields the third resource. */
    resource* r3p = nullptr;
    TEST_ASSERT(STATUS_SUCCESS == queue_pop(q, &r3p));
    TEST_ASSERT(NULL != r3p);

    /* this is the third resource. */
    TEST_EXPECT(r3p == r3h);

    /* the count for the queue should be 0. */
    TEST_EXPECT(0 == queue_count(q));

    /* we should be able to release the queue instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(queue_resource_handle(q)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(r1h));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(r2h));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(r3h));
}
