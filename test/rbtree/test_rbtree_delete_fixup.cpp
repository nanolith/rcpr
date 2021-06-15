/**
 * \file test/rbtree/test_rbtree_delete_fixup.cpp
 *
 * \brief Unit tests for rbtree_delete_fixup.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_delete_fixup);

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
 * Create an empty rbtree, and verify that rbtree_delete_fixup works correctly.
 */
TEST(fixup_empty_tree)
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

    /* perform the delete fixup. */
    rbtree_delete_fixup(tree, tree->nil);

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->nil == tree->root);
    TEST_EXPECT(RBTREE_BLACK == tree->nil->color);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Create an empty rbtree, sub in a single red node, and verify that
 * rbtree_delete_fixup works correctly.
 */
TEST(fixup_single_red_node)
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

    /* perform the delete fixup. */
    rbtree_delete_fixup(tree, &z);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&z == tree->root);
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
 * Create an empty rbtree, sub in a single black node, and verify that
 * rbtree_delete_fixup works correctly.
 */
TEST(fixup_single_black_node)
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
    z.color = RBTREE_BLACK;

    /* perform the delete fixup. */
    rbtree_delete_fixup(tree, &z);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&z == tree->root);
    TEST_EXPECT(RBTREE_BLACK == z.color);
    TEST_EXPECT(RBTREE_BLACK == tree->nil->color);
    TEST_EXPECT(tree->nil == tree->nil->left);
    TEST_EXPECT(tree->nil == tree->nil->right);
    TEST_EXPECT(tree->nil == tree->nil->parent);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
