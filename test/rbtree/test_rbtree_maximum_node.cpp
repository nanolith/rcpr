/**
 * \file test/rbtree/test_rbtree_maximum_node.cpp
 *
 * \brief Unit tests for rbtree_maximum_node.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_maximum_node);

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
 * Verify that rbtree_maximum_node returns the maximum structural node of a
 * given subtree.
 */
TEST(basics)
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

    rbtree_node x;
    rbtree_node y;
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &x;
    x.parent = tree->nil;
    x.left = tree->nil;
    x.right = &y;
    y.parent = &x;
    y.left = tree->nil;
    y.right = &z;
    z.parent = &y;
    z.left = tree->nil;
    z.right = tree->nil;

    /* perform the maximum search. */
    rbtree_node* tmp = rbtree_maximum_node(tree, &x);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&z == tmp);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
