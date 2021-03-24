/**
 * \file test/rbtree/test_rbtree_left_rotate.cpp
 *
 * \brief Unit tests for rbtree_left_rotate.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

TEST_SUITE(rbtree_left_rotate);

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
    parent.left = &x;
    parent.right = tree->nil;
    x.parent = &parent;
    x.left = &alpha;
    x.right = &y;
    y.parent = &x;
    y.left = &beta;
    y.right = &gamma;
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    beta.parent = &y;
    beta.left = tree->nil;
    beta.right = tree->nil;
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;

    /* perform the left rotation. */
    rbtree_left_rotate(tree, &x);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&y == parent.left);
    TEST_EXPECT(tree->nil == parent.right);
    TEST_EXPECT(tree->nil == parent.parent);
    TEST_EXPECT(&y == x.parent);
    TEST_EXPECT(&alpha == x.left);
    TEST_EXPECT(&beta == x.right);
    TEST_EXPECT(&parent == y.parent);
    TEST_EXPECT(&x == y.left);
    TEST_EXPECT(&gamma == y.right);
    TEST_EXPECT(&x == alpha.parent);
    TEST_EXPECT(tree->nil == alpha.left);
    TEST_EXPECT(tree->nil == alpha.right);
    TEST_EXPECT(&x == beta.parent);
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
    parent.left = tree->nil;
    parent.right = &x;
    x.parent = &parent;
    x.left = &alpha;
    x.right = &y;
    y.parent = &x;
    y.left = &beta;
    y.right = &gamma;
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    beta.parent = &y;
    beta.left = tree->nil;
    beta.right = tree->nil;
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;

    /* perform the left rotation. */
    rbtree_left_rotate(tree, &x);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&y == parent.right);
    TEST_EXPECT(tree->nil == parent.left);
    TEST_EXPECT(tree->nil == parent.parent);
    TEST_EXPECT(&y == x.parent);
    TEST_EXPECT(&alpha == x.left);
    TEST_EXPECT(&beta == x.right);
    TEST_EXPECT(&parent == y.parent);
    TEST_EXPECT(&x == y.left);
    TEST_EXPECT(&gamma == y.right);
    TEST_EXPECT(&x == alpha.parent);
    TEST_EXPECT(tree->nil == alpha.left);
    TEST_EXPECT(tree->nil == alpha.right);
    TEST_EXPECT(&x == beta.parent);
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
TEST(rotate_x_root)
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
    tree->root = &x;
    x.parent = tree->nil;
    x.left = &alpha;
    x.right = &y;
    y.parent = &x;
    y.left = &beta;
    y.right = &gamma;
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    beta.parent = &y;
    beta.left = tree->nil;
    beta.right = tree->nil;
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;

    /* perform the left rotation. */
    rbtree_left_rotate(tree, &x);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&y == tree->root);
    TEST_EXPECT(&y == x.parent);
    TEST_EXPECT(&alpha == x.left);
    TEST_EXPECT(&beta == x.right);
    TEST_EXPECT(tree->nil == y.parent);
    TEST_EXPECT(&x == y.left);
    TEST_EXPECT(&gamma == y.right);
    TEST_EXPECT(&x == alpha.parent);
    TEST_EXPECT(tree->nil == alpha.left);
    TEST_EXPECT(tree->nil == alpha.right);
    TEST_EXPECT(&x == beta.parent);
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
