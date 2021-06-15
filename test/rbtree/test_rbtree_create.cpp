/**
 * \file test/rbtree/test_rbtree_create.cpp
 *
 * \brief Unit tests for rbtree_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/rbtree.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_create);

/* dummy comparison. */
static rcpr_comparison_result dummy_compare(
    void* context, const void* lhs, const void* rhs)
{
    return RCPR_COMPARE_LT;
}

/* dummy key function. */
static const void* dummy_key(void* context, const resource* r)
{
    return r;
}

/**
 * Verify that we can create and release an rbtree instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    rbtree* tree = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(&tree, alloc, &dummy_compare, &dummy_key, nullptr));

    /* we should be able to release the rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(rbtree_resource_handle(tree)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
