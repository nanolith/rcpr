/**
 * \file test/rbtree/test_rbtree_right_rotate.cpp
 *
 * \brief Unit tests for rbtree_right_rotate.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_right_rotate);

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
 * Create an rbtree, sub in some nodes, rotate, and test the results.
 */
TEST(rotate_parent_left)
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
    rbtree_node x;
    rbtree_node y;
    rbtree_node alpha;
    rbtree_node beta;
    rbtree_node gamma;

    /* PRECONDITIONS, as per Cormen et al figure 13.2... */
    tree->root = &parent;
    parent.parent = tree->nil;
    parent.left = &y;
    parent.right = tree->nil;
    y.parent = &parent;
    y.right = &gamma;
    y.left = &x;
    x.parent = &y;
    x.left = &alpha;
    x.right = &beta;
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    beta.parent = &x;
    beta.left = tree->nil;
    beta.right = tree->nil;
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;

    /* perform the right rotation. */
    rbtree_right_rotate(tree, &y);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&x == parent.left);
    TEST_EXPECT(tree->nil == parent.right);
    TEST_EXPECT(tree->nil == parent.parent);
    TEST_EXPECT(&parent == x.parent);
    TEST_EXPECT(&alpha == x.left);
    TEST_EXPECT(&y == x.right);
    TEST_EXPECT(&x == y.parent);
    TEST_EXPECT(&beta == y.left);
    TEST_EXPECT(&gamma == y.right);
    TEST_EXPECT(&x == alpha.parent);
    TEST_EXPECT(tree->nil == alpha.left);
    TEST_EXPECT(tree->nil == alpha.right);
    TEST_EXPECT(&y == beta.parent);
    TEST_EXPECT(tree->nil == beta.left);
    TEST_EXPECT(tree->nil == beta.right);
    TEST_EXPECT(&y == gamma.parent);
    TEST_EXPECT(tree->nil == gamma.left);
    TEST_EXPECT(tree->nil == gamma.right);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Create an rbtree, sub in some nodes, rotate, and test the results.
 */
TEST(rotate_parent_right)
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
    rbtree_node x;
    rbtree_node y;
    rbtree_node alpha;
    rbtree_node beta;
    rbtree_node gamma;

    /* PRECONDITIONS, as per Cormen et al figure 13.2... */
    tree->root = &parent;
    parent.parent = tree->nil;
    parent.right = &y;
    parent.left = tree->nil;
    y.parent = &parent;
    y.right = &gamma;
    y.left = &x;
    x.parent = &y;
    x.left = &alpha;
    x.right = &beta;
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    beta.parent = &x;
    beta.left = tree->nil;
    beta.right = tree->nil;
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;

    /* perform the right rotation. */
    rbtree_right_rotate(tree, &y);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&x == parent.right);
    TEST_EXPECT(tree->nil == parent.left);
    TEST_EXPECT(tree->nil == parent.parent);
    TEST_EXPECT(&parent == x.parent);
    TEST_EXPECT(&alpha == x.left);
    TEST_EXPECT(&y == x.right);
    TEST_EXPECT(&x == y.parent);
    TEST_EXPECT(&beta == y.left);
    TEST_EXPECT(&gamma == y.right);
    TEST_EXPECT(&x == alpha.parent);
    TEST_EXPECT(tree->nil == alpha.left);
    TEST_EXPECT(tree->nil == alpha.right);
    TEST_EXPECT(&y == beta.parent);
    TEST_EXPECT(tree->nil == beta.left);
    TEST_EXPECT(tree->nil == beta.right);
    TEST_EXPECT(&y == gamma.parent);
    TEST_EXPECT(tree->nil == gamma.left);
    TEST_EXPECT(tree->nil == gamma.right);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Create an rbtree, sub in some nodes, rotate, and test the results.
 */
TEST(rotate_y_root)
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
    rbtree_node alpha;
    rbtree_node beta;
    rbtree_node gamma;

    /* PRECONDITIONS, as per Cormen et al figure 13.2... */
    tree->root = &y;
    y.parent = tree->nil;
    y.right = &gamma;
    y.left = &x;
    x.parent = &y;
    x.left = &alpha;
    x.right = &beta;
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    beta.parent = &x;
    beta.left = tree->nil;
    beta.right = tree->nil;
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;

    /* perform the right rotation. */
    rbtree_right_rotate(tree, &y);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&x == tree->root);
    TEST_EXPECT(tree->nil == x.parent);
    TEST_EXPECT(&alpha == x.left);
    TEST_EXPECT(&y == x.right);
    TEST_EXPECT(&x == y.parent);
    TEST_EXPECT(&beta == y.left);
    TEST_EXPECT(&gamma == y.right);
    TEST_EXPECT(&x == alpha.parent);
    TEST_EXPECT(tree->nil == alpha.left);
    TEST_EXPECT(tree->nil == alpha.right);
    TEST_EXPECT(&y == beta.parent);
    TEST_EXPECT(tree->nil == beta.left);
    TEST_EXPECT(tree->nil == beta.right);
    TEST_EXPECT(&y == gamma.parent);
    TEST_EXPECT(tree->nil == gamma.left);
    TEST_EXPECT(tree->nil == gamma.right);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
