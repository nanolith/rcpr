/**
 * \file test/rbtree/test_rbtree_left_right_parent_node.cpp
 *
 * \brief Unit tests for rbtree_left_node, rbtree_right_node, and
 * rbtree_parent_node.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/rbtree.h>
#include <rcpr/vtable.h>
#include <stdlib.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_insert);

/* integer resource. */
typedef struct integer integer;
struct integer
{
    resource hdr;
    int val;
};

/* forward decls. */
static status integer_release(resource* r);

/* the vtable entry for the integer instance. */
RCPR_VTABLE
resource_vtable integer_vtable = {
    &integer_release };

/**
 * \brief Release an \ref integer \ref resource.
 *
 * \param r         The \ref integer \ref resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status integer_release(resource* r)
{
    free(r);

    return STATUS_SUCCESS;
}

/**
 * \brief Compare two primitive int keys.
 *
 * \param context   The context to use in this function, if applicable.
 * \param lhs       The left-hand side for this comparison.
 * \param rhs       The right-hand side for this comparison.
 *
 * \returns A comparison result.
 *      - RCPR_COMPARE_LT if lhs < rhs.
 *      - RCPR_COMPARE_GT if lhs > rhs.
 *      - RCPR_COMPARE_EQ if lhs == rhs.
 */
static rcpr_comparison_result integer_compare(
    void*, const void* lhs, const void* rhs)
{
    const int* l = (const int*)lhs; const int* r = (const int*)rhs;

    if (*l < *r)
        return RCPR_COMPARE_LT;
    else if (*l > *r)
        return RCPR_COMPARE_GT;
    else
        return RCPR_COMPARE_EQ;
}

/**
 * \brief Extract the pointer to a primitive integer key from an \ref integer
 * \ref resource.
 *
 * \param context   The context to use in this function, if applicable.
 * \param r         The integer resource from which this key value should be
 *                  extracted.
 *
 * \returns a const void pointer to the integer primitive value.
 */
static const void* integer_key(void*, const resource* r)
{
    const integer* i = (const integer*)r;

    return &i->val;
}

/**
 * The parent node of a nil node is nil.
 */
TEST(parent_nil)
{
    allocator* alloc = nullptr;
    rbtree* tree = nullptr;
    rbtree_node* nil;
    rbtree_node* root;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &tree, alloc, &integer_compare, &integer_key, nullptr));

    /* get the nil node. */
    nil = rbtree_nil_node(tree);

    /* get the root node. */
    root = rbtree_root_node(tree);

    /* root is nil. */
    TEST_ASSERT(nil == root);

    /* the parent of root is nil. */
    TEST_ASSERT(nil == rbtree_parent_node(tree, root));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
