/**
 * \file test/rbtree/test_rbtree_delete_fixup.cpp
 *
 * \brief Unit tests for rbtree_delete_fixup.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>

#include "../../src/rbtree/rbtree_internal.h"

TEST_SUITE(rbtree_delete);

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

/* dummy resource release function. */
static status dummy_release(resource* r)
{
    return STATUS_SUCCESS;
}

/**
 * Delete the only node in a tree.
 */
TEST(delete_root)
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
    z.hdr.release = &dummy_release;

    /* Delete this node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &z));

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
 * Delete the child of a two node tree.
 */
TEST(delete_child_two_nodes)
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

    rbtree_node p;
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &p;
    p.parent = tree->nil;
    p.left = &z;
    p.right = tree->nil;
    p.color = RBTREE_BLACK;
    p.hdr.release = &dummy_release;
    z.parent = &p;
    z.left = tree->nil;
    z.right = tree->nil;
    z.color = RBTREE_RED;
    z.hdr.release = &dummy_release;

    /* Delete the child node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &z));

    /* POSTCONDITIONS. */
    TEST_EXPECT(&p == tree->root);
    TEST_EXPECT(p.color == RBTREE_BLACK);
    TEST_EXPECT(p.left == tree->nil);
    TEST_EXPECT(p.right == tree->nil);
    TEST_EXPECT(p.parent == tree->nil);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete the root of a two node tree.
 */
TEST(delete_root_two_nodes)
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

    rbtree_node p;
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &p;
    p.parent = tree->nil;
    p.left = &z;
    p.right = tree->nil;
    p.color = RBTREE_BLACK;
    p.hdr.release = &dummy_release;
    z.parent = &p;
    z.left = tree->nil;
    z.right = tree->nil;
    z.color = RBTREE_RED;
    z.hdr.release = &dummy_release;

    /* Delete the child node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &p));

    /* POSTCONDITIONS. */
    TEST_EXPECT(&z == tree->root);
    TEST_EXPECT(z.color == RBTREE_BLACK);
    TEST_EXPECT(z.left == tree->nil);
    TEST_EXPECT(z.right == tree->nil);
    TEST_EXPECT(z.parent == tree->nil);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete the left child of a three node tree.
 */
TEST(delete_left_three_nodes)
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

    rbtree_node p;
    rbtree_node y;
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &p;
    p.parent = tree->nil;
    p.left = &z;
    p.right = &y;
    p.color = RBTREE_BLACK;
    p.hdr.release = &dummy_release;
    z.parent = &p;
    z.left = tree->nil;
    z.right = tree->nil;
    z.color = RBTREE_RED;
    z.hdr.release = &dummy_release;
    y.parent = &p;
    y.left = tree->nil;
    y.right = tree->nil;
    y.color = RBTREE_RED;
    y.hdr.release = &dummy_release;

    /* Delete the child node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &z));

    /* POSTCONDITIONS. */
    TEST_EXPECT(&p == tree->root);
    TEST_EXPECT(p.parent == tree->nil);
    TEST_EXPECT(p.color == RBTREE_BLACK);
    TEST_EXPECT(p.left == tree->nil);
    TEST_EXPECT(p.right == &y);
    TEST_EXPECT(y.parent == &p);
    TEST_EXPECT(y.color == RBTREE_RED);
    TEST_EXPECT(y.left == tree->nil);
    TEST_EXPECT(y.right == tree->nil);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete the right child of a three node tree.
 */
TEST(delete_right_three_nodes)
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

    rbtree_node p;
    rbtree_node y;
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &p;
    p.parent = tree->nil;
    p.left = &z;
    p.right = &y;
    p.color = RBTREE_BLACK;
    p.hdr.release = &dummy_release;
    z.parent = &p;
    z.left = tree->nil;
    z.right = tree->nil;
    z.color = RBTREE_RED;
    z.hdr.release = &dummy_release;
    y.parent = &p;
    y.left = tree->nil;
    y.right = tree->nil;
    y.color = RBTREE_RED;
    y.hdr.release = &dummy_release;

    /* Delete the child node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &y));

    /* POSTCONDITIONS. */
    TEST_EXPECT(&p == tree->root);
    TEST_EXPECT(p.parent == tree->nil);
    TEST_EXPECT(p.color == RBTREE_BLACK);
    TEST_EXPECT(p.left == &z);
    TEST_EXPECT(p.right == tree->nil);
    TEST_EXPECT(z.parent == &p);
    TEST_EXPECT(z.color == RBTREE_RED);
    TEST_EXPECT(z.left == tree->nil);
    TEST_EXPECT(z.right == tree->nil);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete the root of a three node tree.
 */
TEST(delete_root_three_nodes)
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

    rbtree_node p;
    rbtree_node y;
    rbtree_node z;

    /* PRECONDITIONS. */
    tree->root = &p;
    p.parent = tree->nil;
    p.left = &z;
    p.right = &y;
    p.color = RBTREE_BLACK;
    p.hdr.release = &dummy_release;
    z.parent = &p;
    z.left = tree->nil;
    z.right = tree->nil;
    z.color = RBTREE_RED;
    z.hdr.release = &dummy_release;
    y.parent = &p;
    y.left = tree->nil;
    y.right = tree->nil;
    y.color = RBTREE_RED;
    y.hdr.release = &dummy_release;

    /* Delete the child node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &p));

    /* POSTCONDITIONS. */
    TEST_EXPECT(&y == tree->root);
    TEST_EXPECT(y.parent == tree->nil);
    TEST_EXPECT(y.color == RBTREE_BLACK);
    TEST_EXPECT(y.left == &z);
    TEST_EXPECT(y.right == tree->nil);
    TEST_EXPECT(z.parent == &y);
    TEST_EXPECT(z.color == RBTREE_RED);
    TEST_EXPECT(z.left == tree->nil);
    TEST_EXPECT(z.right == tree->nil);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
