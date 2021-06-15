/**
 * \file test/rbtree/test_rbtree_successor_node.cpp
 *
 * \brief Unit tests for rbtree_successor_node.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_successor_node);

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
 * Verify that rbtree_successor_node returns the next successor for each node.
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

    /* nodes 1 through 10. */
    rbtree_node node1;
    rbtree_node node2;
    rbtree_node node3;
    rbtree_node node4;
    rbtree_node node5;
    rbtree_node node6;
    rbtree_node node7;
    rbtree_node node8;
    rbtree_node node9;
    rbtree_node node10;
    rbtree_node node11;
    rbtree_node node12;
    rbtree_node node13;
    rbtree_node node14;
    rbtree_node node15;

    /* 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 */

    /* build up a balanced tree. */
    tree->root = &node8;
    node8.parent = tree->nil;
    node8.left = &node4;
    node8.right = &node12;
    node4.parent = &node8;
    node4.left = &node2;
    node4.right = &node6;
    node2.parent = &node4;
    node2.left = &node1;
    node2.right = &node3;
    node1.parent = &node2;
    node1.left = tree->nil;
    node1.right = tree->nil;
    node3.parent = &node2;
    node3.left = tree->nil;
    node3.right = tree->nil;
    node6.parent = &node4;
    node6.left = &node5;
    node6.right = &node7;
    node5.parent = &node6;
    node5.left = tree->nil;
    node5.right = tree->nil;
    node7.parent = &node6;
    node7.left = tree->nil;
    node7.right = tree->nil;
    node12.parent = &node8;
    node12.left = &node10;
    node12.right = &node14;
    node10.parent = &node12;
    node10.left = &node9;
    node10.right = &node11;
    node9.parent = &node10;
    node9.left = tree->nil;
    node9.right = tree->nil;
    node11.parent = &node10;
    node11.left = tree->nil;
    node11.right = tree->nil;
    node14.parent = &node12;
    node14.left = &node13;
    node14.right = &node15;
    node13.parent = &node14;
    node13.left = tree->nil;
    node13.right = tree->nil;
    node15.parent = &node14;
    node15.left = tree->nil;
    node15.right = tree->nil;

    /* iterate through successors, starting with node1. */
    TEST_ASSERT(&node2 == rbtree_successor_node(tree, &node1));
    TEST_ASSERT(&node3 == rbtree_successor_node(tree, &node2));
    TEST_ASSERT(&node4 == rbtree_successor_node(tree, &node3));
    TEST_ASSERT(&node5 == rbtree_successor_node(tree, &node4));
    TEST_ASSERT(&node6 == rbtree_successor_node(tree, &node5));
    TEST_ASSERT(&node7 == rbtree_successor_node(tree, &node6));
    TEST_ASSERT(&node8 == rbtree_successor_node(tree, &node7));
    TEST_ASSERT(&node9 == rbtree_successor_node(tree, &node8));
    TEST_ASSERT(&node10 == rbtree_successor_node(tree, &node9));
    TEST_ASSERT(&node11 == rbtree_successor_node(tree, &node10));
    TEST_ASSERT(&node12 == rbtree_successor_node(tree, &node11));
    TEST_ASSERT(&node13 == rbtree_successor_node(tree, &node12));
    TEST_ASSERT(&node14 == rbtree_successor_node(tree, &node13));
    TEST_ASSERT(&node15 == rbtree_successor_node(tree, &node14));
    TEST_ASSERT(tree->nil == rbtree_successor_node(tree, &node15));

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
