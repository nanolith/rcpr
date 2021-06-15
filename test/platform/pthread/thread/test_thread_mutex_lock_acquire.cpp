/**
 * \file test/platform/pthread/thread/test_thread_mutex_lock_acquire.cpp
 *
 * \brief Unit tests for thread_mutex_lock_acquire.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/thread.h>
#include <string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(thread_mutex_lock_acquire);

/**
 * Verify that we can acquire a mutex lock.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    thread_mutex* mut = nullptr;
    thread_mutex_lock* lock = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a thread mutex. */
    TEST_ASSERT(STATUS_SUCCESS == thread_mutex_create(&mut, alloc));

    /* we should be able to acquire the thread mutex lock. */
    TEST_ASSERT(STATUS_SUCCESS == thread_mutex_lock_acquire(&lock, mut));

    /* we should be able to release the thread mutex lock. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(thread_mutex_lock_resource_handle(lock)));

    /* we should be able to release a thread mutex. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_mutex_resource_handle(mut)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
