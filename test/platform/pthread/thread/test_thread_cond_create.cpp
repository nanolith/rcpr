/**
 * \file test/platform/pthread/thread/test_thread_cond_create.cpp
 *
 * \brief Unit tests for thread_cond_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/thread.h>
#include <string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

TEST_SUITE(thread_cond_create);

/**
 * Verify that we can create a \ref thread_cond.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    thread_cond* cond = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a thread cond. */
    TEST_ASSERT(STATUS_SUCCESS == thread_cond_create(&cond, alloc));

    /* we should be able to release a thread cond. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_cond_resource_handle(cond)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
