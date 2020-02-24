/**
 * \file test/test_malloc_allocator.cpp
 *
 * \brief Unit tests for malloc allocator.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

TEST_SUITE(malloc_allocator);

/**
 * Verify that we can create and release a malloc allocator.
 */
TEST(create_release)
{
    allocator* alloc = nullptr;
    resource* alloc_resource = nullptr;

    /* we can successfully create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* the allocator pointer is valid. */
    TEST_ASSERT(
        nullptr != alloc);

    /* get the allocator resource handle. */
    alloc_resource = allocator_resource_handle(alloc);

    /* this resource handle is valid. */
    TEST_ASSERT(
        nullptr != alloc_resource);

    /* we can release this resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(alloc_resource));
}

/**
 * Verify that we can allocate, reallocate, and reclaim memory.
 */
TEST(alloc_realloc_free)
{
    allocator* alloc = nullptr;
    int* arr = nullptr;

    /* we can create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we can allocate an array. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_allocate(alloc, (void**)&arr, 10*sizeof(int)));

    /* we can resize the array larger. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_reallocate(alloc, (void**)&arr, 20*sizeof(int)));

    /* we can resize the array smaller. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_reallocate(alloc, (void**)&arr, 5*sizeof(int)));

    /* we can reclaim the array. */
    TEST_ASSERT(
        STATUS_SUCCESS == allocator_reclaim(alloc, arr));

    /* we can release this resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
