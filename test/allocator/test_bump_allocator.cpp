/**
 * \file test/test_bump_allocator.cpp
 *
 * \brief Unit tests for bump allocator.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <stdalign.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(bump_allocator);

/**
 * Verify that we can create and release a bump allocator.
 */
TEST(create_release)
{
    allocator* alloc = nullptr;
    resource* alloc_resource = nullptr;
    alignas(16) char region[1024];

    /* we can successfully create a bump allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == bump_allocator_create(&alloc, region, sizeof(region)));

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
 * Verify that we can allocate and reclaim memory.
 */
TEST(alloc_reclaim)
{
    allocator* alloc = nullptr;
    int* var = nullptr;
    alignas(16) char region[1024];

    /* we can create a bump allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == bump_allocator_create(&alloc, region, sizeof(region)));

    /* we can allocate an int. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_allocate(alloc, (void**)&var, sizeof(*var)));
    TEST_ASSERT(nullptr != var);

    *var = 10;
    TEST_EXPECT(10 == *var);

    /* we can reclaim the var (no-op for a bump allocator). */
    TEST_ASSERT(
        STATUS_SUCCESS == allocator_reclaim(alloc, var));

    /* we can release this resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can allocate, reset, and allocate again.
 */
TEST(alloc_reset)
{
    allocator* alloc = nullptr;
    int* var1 = nullptr;
    int* var2 = nullptr;
    alignas(16) char region[1024];

    /* we can create a bump allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == bump_allocator_create(&alloc, region, sizeof(region)));

    /* we can allocate an int. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_allocate(alloc, (void**)&var1, sizeof(*var1)));
    TEST_ASSERT(nullptr != var1);

    /* we can reset the bump allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS
                == allocator_control(
                        alloc, RCPR_ALLOCATOR_CONTROL_BUMP_ALLOCATOR_RESET,
                        nullptr, 0));

    /* we can allocate an int. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_allocate(alloc, (void**)&var2, sizeof(*var2)));
    TEST_ASSERT(nullptr != var2);

    /* because the bump allocator was reset, var1 and var2 are aliased. */
    TEST_ASSERT(var1 == var2);

    /* we can release this resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
