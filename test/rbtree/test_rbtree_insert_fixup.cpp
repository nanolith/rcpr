/**
 * \file test/rbtree/test_rbtree_insert_fixup.cpp
 *
 * \brief Unit tests for rbtree_insert_fixup.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_insert_fixup);

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
 * Create an rbtree, sub in a single node, and verify that rbtree_insert_fixup
 * works correctly.
 */
TEST(fixup_single_node)
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

    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &z;
    z.parent = tree->nil;
    z.left = tree->nil;
    z.right = tree->nil;
    z.color = RBTREE_RED;

    /* perform the insert fixup. */
    rbtree_insert_fixup(tree, &z);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&z == tree->root);
    TEST_EXPECT(tree->nil == z.left);
    TEST_EXPECT(tree->nil == z.right);
    TEST_EXPECT(RBTREE_BLACK == z.color);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Demonstrate that our implementation resolves as per figure 13.4 in Cormen et
 * al.
 */
TEST(fixup_example_13_4)
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

    rbtree_node node1;
    rbtree_node node2;
    rbtree_node node4;
    rbtree_node node5;
    rbtree_node node7;
    rbtree_node node8;
    rbtree_node node11;
    rbtree_node node14;
    rbtree_node node15;

    /* PRECONDITIONS. */
    tree->root = &node11;

    node11.parent = tree->nil;
    node11.left = &node2;
    node11.right = &node14;
    node11.color = RBTREE_BLACK;

    node2.parent = &node11;
    node2.left = &node1;
    node2.right = &node7;
    node2.color = RBTREE_RED;

    node1.parent = &node2;
    node1.left = tree->nil;
    node1.right = tree->nil;
    node1.color = RBTREE_BLACK;

    node7.parent = &node2;
    node7.left = &node5;
    node7.right = &node8;
    node7.color = RBTREE_BLACK;

    node8.parent = &node7;
    node8.left = tree->nil;
    node8.right = tree->nil;
    node8.color = RBTREE_RED;

    node5.parent = &node7;
    node5.left = &node4;
    node5.right = tree->nil;
    node5.color = RBTREE_RED;

    node4.parent = &node5;
    node4.left = tree->nil;
    node4.right = tree->nil;
    node4.color = RBTREE_RED;

    node14.parent = &node11;
    node14.left = tree->nil;
    node14.right = &node15;
    node14.color = RBTREE_BLACK;

    node15.parent = &node14;
    node15.left = tree->nil;
    node15.right = tree->nil;
    node15.color = RBTREE_RED;

    /* perform the insert fixup. */
    rbtree_insert_fixup(tree, &node4);

    /* POSTCONDITIONS. */
    TEST_ASSERT(&node7 == tree->root);
    TEST_ASSERT(&node2 == node7.left);
    TEST_ASSERT(&node11 == node7.right);
    TEST_ASSERT(RBTREE_BLACK == node7.color);

    TEST_ASSERT(&node7 == node2.parent);
    TEST_ASSERT(&node1 == node2.left);
    TEST_ASSERT(&node5 == node2.right);
    TEST_ASSERT(RBTREE_RED == node2.color);

    TEST_ASSERT(&node2 == node1.parent);
    TEST_ASSERT(tree->nil == node1.left);
    TEST_ASSERT(tree->nil == node1.right);
    TEST_ASSERT(RBTREE_BLACK == node1.color);

    TEST_ASSERT(&node2 == node5.parent);
    TEST_ASSERT(&node4 == node5.left);
    TEST_ASSERT(tree->nil == node5.right);
    TEST_ASSERT(RBTREE_BLACK == node5.color);

    TEST_ASSERT(&node5 == node4.parent);
    TEST_ASSERT(tree->nil == node4.left);
    TEST_ASSERT(tree->nil == node4.right);
    TEST_ASSERT(RBTREE_RED == node4.color);

    TEST_ASSERT(&node7 == node11.parent);
    TEST_ASSERT(&node8 == node11.left);
    TEST_ASSERT(&node14 == node11.right);
    TEST_ASSERT(RBTREE_RED == node11.color);

    TEST_ASSERT(&node11 == node8.parent);
    TEST_ASSERT(tree->nil == node8.left);
    TEST_ASSERT(tree->nil == node8.right);
    TEST_ASSERT(RBTREE_BLACK == node8.color);

    TEST_ASSERT(&node11 == node14.parent);
    TEST_ASSERT(tree->nil == node14.left);
    TEST_ASSERT(&node15 == node14.right);
    TEST_ASSERT(RBTREE_BLACK == node14.color);

    TEST_ASSERT(&node14 == node15.parent);
    TEST_ASSERT(tree->nil == node15.left);
    TEST_ASSERT(tree->nil == node15.right);
    TEST_ASSERT(RBTREE_RED == node15.color);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
