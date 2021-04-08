/**
 * \file test/rbtree/test_rbtree_delete.cpp
 *
 * \brief Unit tests for rbtree_delete_node.
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

/**
 * Delete leaf 15 of a 15 node tree.
 */
TEST(delete_leaf15_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n15));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n2);
    TEST_EXPECT(n3.left == tree->nil);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == tree->nil);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 13 of a 15 node tree.
 */
TEST(delete_leaf13_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n13));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n2);
    TEST_EXPECT(n3.left == tree->nil);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == tree->nil);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 11 of a 15 node tree.
 */
TEST(delete_leaf11_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n11));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n2);
    TEST_EXPECT(n3.left == tree->nil);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == tree->nil);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 9 of a 15 node tree.
 */
TEST(delete_leaf9_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n9));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n2);
    TEST_EXPECT(n3.left == tree->nil);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == tree->nil);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 7 of a 15 node tree.
 */
TEST(delete_leaf7_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n7));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n2);
    TEST_EXPECT(n3.left == tree->nil);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == tree->nil);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 5 of a 15 node tree.
 */
TEST(delete_leaf5_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n5));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n2);
    TEST_EXPECT(n3.left == tree->nil);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == tree->nil);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 3 of a 15 node tree.
 */
TEST(delete_leaf3_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n3));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == tree->nil);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete leaf 1 of a 15 node tree.
 */
TEST(delete_leaf1_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n1));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == tree->nil);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 2 of a 15 node tree.
 */
TEST(delete_branch2_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n2));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n3);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n3.parent == &n4);
    TEST_EXPECT(n3.left == &n1);
    TEST_EXPECT(n3.right == tree->nil);
    TEST_EXPECT(n3.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n3);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 6 of a 15 node tree.
 */
TEST(delete_branch6_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n6));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n7);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n7.parent == &n4);
    TEST_EXPECT(n7.left == &n5);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n7);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 10 of a 15 node tree.
 */
TEST(delete_branch10_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n10));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n11);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n12);
    TEST_EXPECT(n11.left == &n9);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n11);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 14 of a 15 node tree.
 */
TEST(delete_branch14_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n14));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n15);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n12);
    TEST_EXPECT(n15.left == &n13);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n15);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 4 of a 15 node tree.
 */
TEST(delete_branch4_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n4));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n5);
    TEST_EXPECT(n8.right == &n12);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n8);
    TEST_EXPECT(n5.left == &n2);
    TEST_EXPECT(n5.right == &n6);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n5);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n6.parent == &n5);
    TEST_EXPECT(n6.left == tree->nil);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n8);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 12 of a 15 node tree.
 */
TEST(delete_branch12_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n12));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n8);
    TEST_EXPECT(n8.parent == tree->nil);
    TEST_EXPECT(n8.left == &n4);
    TEST_EXPECT(n8.right == &n13);
    TEST_EXPECT(n8.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n8);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n13.parent == &n8);
    TEST_EXPECT(n13.left == &n10);
    TEST_EXPECT(n13.right == &n14);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n13);
    TEST_EXPECT(n10.left == &n9);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n9.parent == &n10);
    TEST_EXPECT(n9.left == tree->nil);
    TEST_EXPECT(n9.right == tree->nil);
    TEST_EXPECT(n9.color == RBTREE_RED);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n13);
    TEST_EXPECT(n14.left == tree->nil);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Delete branch 8 of a 15 node tree.
 */
TEST(delete_branch8_fifteen_nodes)
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

    rbtree_node n1;
    rbtree_node n2;
    rbtree_node n3;
    rbtree_node n4;
    rbtree_node n5;
    rbtree_node n6;
    rbtree_node n7;
    rbtree_node n8;
    rbtree_node n9;
    rbtree_node n10;
    rbtree_node n11;
    rbtree_node n12;
    rbtree_node n13;
    rbtree_node n14;
    rbtree_node n15;

    /* PRECONDITIONS. */
    tree->root = &n8;
    n8.parent = tree->nil;
    n8.left = &n4;
    n8.right = &n12;
    n8.color = RBTREE_BLACK;
    n8.hdr.release = &dummy_release;
    n4.parent = &n8;
    n4.left = &n2;
    n4.right = &n6;
    n4.color = RBTREE_RED;
    n4.hdr.release = &dummy_release;
    n2.parent = &n4;
    n2.left = &n1;
    n2.right = &n3;
    n2.color = RBTREE_BLACK;
    n2.hdr.release = &dummy_release;
    n1.parent = &n2;
    n1.left = tree->nil;
    n1.right = tree->nil;
    n1.color = RBTREE_RED;
    n1.hdr.release = &dummy_release;
    n3.parent = &n2;
    n3.left = tree->nil;
    n3.right = tree->nil;
    n3.color = RBTREE_RED;
    n3.hdr.release = &dummy_release;
    n6.parent = &n4;
    n6.left = &n5;
    n6.right = &n7;
    n6.color = RBTREE_BLACK;
    n6.hdr.release = &dummy_release;
    n5.parent = &n6;
    n5.left = tree->nil;
    n5.right = tree->nil;
    n5.color = RBTREE_RED;
    n5.hdr.release = &dummy_release;
    n7.parent = &n6;
    n7.left = tree->nil;
    n7.right = tree->nil;
    n7.color = RBTREE_RED;
    n7.hdr.release = &dummy_release;
    n12.parent = &n8;
    n12.left = &n10;
    n12.right = &n14;
    n12.color = RBTREE_RED;
    n12.hdr.release = &dummy_release;
    n10.parent = &n12;
    n10.left = &n9;
    n10.right = &n11;
    n10.color = RBTREE_BLACK;
    n10.hdr.release = &dummy_release;
    n9.parent = &n10;
    n9.left = tree->nil;
    n9.right = tree->nil;
    n9.color = RBTREE_RED;
    n9.hdr.release = &dummy_release;
    n11.parent = &n10;
    n11.left = tree->nil;
    n11.right = tree->nil;
    n11.color = RBTREE_RED;
    n11.hdr.release = &dummy_release;
    n14.parent = &n12;
    n14.left = &n13;
    n14.right = &n15;
    n14.color = RBTREE_BLACK;
    n14.hdr.release = &dummy_release;
    n13.parent = &n14;
    n13.left = tree->nil;
    n13.right = tree->nil;
    n13.color = RBTREE_RED;
    n13.hdr.release = &dummy_release;
    n15.parent = &n14;
    n15.left = tree->nil;
    n15.right = tree->nil;
    n15.color = RBTREE_RED;
    n15.hdr.release = &dummy_release;

    /* Delete a leaf node. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_delete_node(tree, &n8));

    /* POSTCONDITIONS. */
    TEST_EXPECT(tree->root == &n9);
    TEST_EXPECT(n9.parent == tree->nil);
    TEST_EXPECT(n9.left == &n4);
    TEST_EXPECT(n9.right == &n12);
    TEST_EXPECT(n9.color == RBTREE_BLACK);
    TEST_EXPECT(n4.parent == &n9);
    TEST_EXPECT(n4.left == &n2);
    TEST_EXPECT(n4.right == &n6);
    TEST_EXPECT(n4.color == RBTREE_RED);
    TEST_EXPECT(n2.parent == &n4);
    TEST_EXPECT(n2.left == &n1);
    TEST_EXPECT(n2.right == &n3);
    TEST_EXPECT(n2.color == RBTREE_BLACK);
    TEST_EXPECT(n1.parent == &n2);
    TEST_EXPECT(n1.left == tree->nil);
    TEST_EXPECT(n1.right == tree->nil);
    TEST_EXPECT(n1.color == RBTREE_RED);
    TEST_EXPECT(n3.parent = &n2);
    TEST_EXPECT(n3.left = tree->nil);
    TEST_EXPECT(n3.right = tree->nil);
    TEST_EXPECT(n3.color = RBTREE_RED);
    TEST_EXPECT(n6.parent == &n4);
    TEST_EXPECT(n6.left == &n5);
    TEST_EXPECT(n6.right == &n7);
    TEST_EXPECT(n6.color == RBTREE_BLACK);
    TEST_EXPECT(n5.parent == &n6);
    TEST_EXPECT(n5.left == tree->nil);
    TEST_EXPECT(n5.right == tree->nil);
    TEST_EXPECT(n5.color == RBTREE_RED);
    TEST_EXPECT(n7.parent == &n6);
    TEST_EXPECT(n7.left == tree->nil);
    TEST_EXPECT(n7.right == tree->nil);
    TEST_EXPECT(n7.color == RBTREE_RED);
    TEST_EXPECT(n12.parent == &n9);
    TEST_EXPECT(n12.left == &n10);
    TEST_EXPECT(n12.right == &n14);
    TEST_EXPECT(n12.color == RBTREE_RED);
    TEST_EXPECT(n10.parent == &n12);
    TEST_EXPECT(n10.left == tree->nil);
    TEST_EXPECT(n10.right == &n11);
    TEST_EXPECT(n10.color == RBTREE_BLACK);
    TEST_EXPECT(n11.parent == &n10);
    TEST_EXPECT(n11.left == tree->nil);
    TEST_EXPECT(n11.right == tree->nil);
    TEST_EXPECT(n11.color == RBTREE_RED);
    TEST_EXPECT(n14.parent == &n12);
    TEST_EXPECT(n14.left == &n13);
    TEST_EXPECT(n14.right == &n15);
    TEST_EXPECT(n14.color == RBTREE_BLACK);
    TEST_EXPECT(n13.parent == &n14);
    TEST_EXPECT(n13.left == tree->nil);
    TEST_EXPECT(n13.right == tree->nil);
    TEST_EXPECT(n13.color == RBTREE_RED);
    TEST_EXPECT(n15.parent == &n14);
    TEST_EXPECT(n15.left == tree->nil);
    TEST_EXPECT(n15.right == tree->nil);
    TEST_EXPECT(n15.color == RBTREE_RED);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
