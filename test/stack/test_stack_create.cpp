/**
 * \file test/stack/test_stack_create.cpp
 *
 * \brief Unit tests for stack_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/stack.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(stack_create);

/**
 * Verify that we can create and release a stack instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    stack* st = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a stack. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            stack_create(
                &st, alloc, 1024 * 1024));

    /* we should be able to release the stack instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(stack_resource_handle(st)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
