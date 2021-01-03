/**
 * \file test/test_queue_create.cpp
 *
 * \brief Unit tests for queue_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/queue.h>

TEST_SUITE(queue_create);

/**
 * Verify that we can create and release a queue instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    queue* q = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a queue. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            queue_create(
                &q, alloc));

    /* the queue count should be zero. */
    TEST_ASSERT(0U == queue_count(q));

    /* we should be able to release the queue instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(queue_resource_handle(q)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
