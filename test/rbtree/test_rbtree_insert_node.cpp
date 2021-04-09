/**
 * \file test/rbtree/test_rbtree_insert_node.cpp
 *
 * \brief Unit tests for rbtree_insert_node.
 */

#include <cstring>
#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

TEST_SUITE(rbtree_insert_node);

using namespace std;

/* dummy comparison. */
static rcpr_comparison_result dummy_compare(
    void* context, const void* lhs, const void* rhs)
{
    if (((int64_t)lhs) < ((int64_t)rhs))
    {
        return RCPR_COMPARE_LT;
    }
    else if (((int64_t)lhs) > ((int64_t)rhs))
    {
        return RCPR_COMPARE_GT;
    }
    else
    {
        return RCPR_COMPARE_EQ;
    }
}

/* dummy key function. */
static const void* dummy_key(void* context, const resource* r)
{
    return r;
}

/**
 * Insert a node into an empty tree.
 */
TEST(insert_empty)
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
    memset(&z, 0, sizeof(rbtree_node));
    z.value = (resource*)1;

    /* Insert this node into the tree. */
    rbtree_insert_node(tree, &z);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&z == tree->root);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Insert a node smaller than the root.
 */
TEST(insert_left)
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
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &parent;
    parent.parent = tree->nil;
    parent.left = tree->nil;
    parent.right = tree->nil;
    parent.color = RBTREE_BLACK;
    parent.value = (resource*)10;
    memset(&z, 0, sizeof(rbtree_node));
    z.value = (resource*)1;

    /* Insert this node into the tree. */
    rbtree_insert_node(tree, &z);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(&z == parent.left);
    TEST_EXPECT(tree->nil == parent.right);
    TEST_EXPECT(RBTREE_BLACK == parent.color);
    TEST_EXPECT(&parent == z.parent);
    TEST_EXPECT(tree->nil == z.left);
    TEST_EXPECT(tree->nil == z.right);
    TEST_EXPECT(RBTREE_RED == z.color);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Insert a node larger than the root.
 */
TEST(insert_right)
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
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &parent;
    parent.parent = tree->nil;
    parent.left = tree->nil;
    parent.right = tree->nil;
    parent.color = RBTREE_BLACK;
    parent.value = (resource*)10;
    memset(&z, 0, sizeof(rbtree_node));
    z.value = (resource*)20;

    /* Insert this node into the tree. */
    rbtree_insert_node(tree, &z);

    /* POSTCONDITIONS. */
    TEST_EXPECT(&parent == tree->root);
    TEST_EXPECT(tree->nil == parent.left);
    TEST_EXPECT(&z == parent.right);
    TEST_EXPECT(RBTREE_BLACK == parent.color);
    TEST_EXPECT(&parent == z.parent);
    TEST_EXPECT(tree->nil == z.left);
    TEST_EXPECT(tree->nil == z.right);
    TEST_EXPECT(RBTREE_RED == z.color);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
