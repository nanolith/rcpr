/**
 * \file test/rbtree/test_rbtree_transplant.cpp
 *
 * \brief Unit tests for rbtree_transplant.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_transplant);

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
 * Verify that v becomes the new root if u is the root.
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

    rbtree_node u;
    rbtree_node v;

    /* PRECONDITIONS. */
    tree->root = &u;
    u.parent = tree->nil;
    u.left = &v;
    u.right = tree->nil;
    v.parent = &u;
    v.left = tree->nil;
    v.right = tree->nil;

    /* perform the transplant. */
    rbtree_transplant(tree, &u, &v);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&v == tree->root);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that tree->nil becomes the new root if u is the root and v is nil.
 */
TEST(nil_v)
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

    rbtree_node u;

    /* PRECONDITIONS. */
    tree->root = &u;
    u.parent = tree->nil;
    u.left = tree->nil;
    u.right = tree->nil;

    /* perform the transplant. */
    rbtree_transplant(tree, &u, tree->nil);

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->nil == tree->root);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Test transplant when &u is u.parent->left.
 */
TEST(u_parent_left)
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

    rbtree_node parent;
    rbtree_node u;
    rbtree_node v;

    /* PRECONDITIONS. */
    tree->root = &parent;
    parent.parent = tree->nil;
    parent.left = &u;
    parent.right = tree->nil;
    u.parent = &parent;
    u.left = &v;
    u.right = tree->nil;
    v.parent = &u;
    v.left = tree->nil;
    v.right = tree->nil;

    /* perform the transplant. */
    rbtree_transplant(tree, &u, &v);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&v == parent.left);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Test transplant when &u is u.parent->right.
 */
TEST(u_parent_right)
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

    rbtree_node parent;
    rbtree_node u;
    rbtree_node v;

    /* PRECONDITIONS. */
    tree->root = &parent;
    parent.parent = tree->nil;
    parent.left = tree->nil;
    parent.right = &u;
    u.parent = &parent;
    u.left = &v;
    u.right = tree->nil;
    v.parent = &u;
    v.left = tree->nil;
    v.right = tree->nil;

    /* perform the transplant. */
    rbtree_transplant(tree, &u, &v);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&v == parent.right);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
