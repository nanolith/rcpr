/**
 * \file test/rbtree/test_rbtree_clear.cpp
 *
 * \brief Unit tests for rbtree_clear.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/rbtree.h>
#include <stdlib.h>

#include "../../src/resource/resource_internal.h"

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
 * \brief Create an \ref integer \ref resource from a primitive int.
 *
 * \param i         Pointer to a pointer to receive the integer resource on
 *                  success.
 * \param value     The primitive integer value to box in this type.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status FN_DECL_MUST_CHECK integer_create(integer** i, int value)
{
    integer* tmp;

    /* allocate space for the integer instance. */
    tmp = (integer*)malloc(sizeof(integer));
    if (NULL == tmp)
    {
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    /* initialize the integer resource. */
    resource_init(&tmp->hdr, &integer_release);

    /* set the value. */
    tmp->val = value;
    *i = tmp;

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
 * Clearing an empty rbtree instance should succeed.
 */
TEST(clear_empty)
{
    allocator* alloc = nullptr;
    rbtree* tree = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &tree, alloc, &integer_compare, &integer_key, nullptr));

    /* we should be able to clear the rbtree instance. */
    TEST_EXPECT(STATUS_SUCCESS == rbtree_clear(tree));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Insert ten integers into a list and clear the list.
 */
TEST(insert_ints)
{
    allocator* alloc = nullptr;
    rbtree* tree = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &tree, alloc, &integer_compare, &integer_key, nullptr));

    /* insert integers. */
    for (int i = 0; i < 10; ++i)
    {
        integer* value = nullptr;

        /* we should be able to insert an integer. */
        TEST_ASSERT(
            STATUS_SUCCESS == integer_create(&value, i));

        /* insert the integer. */
        TEST_ASSERT(
            STATUS_SUCCESS == rbtree_insert(tree, &value->hdr));
    }

    /* the rbtree count is now 10. */
    TEST_ASSERT(10 == rbtree_count(tree));

    /* we can clear the rbtree. */
    TEST_EXPECT(
        STATUS_SUCCESS == rbtree_clear(tree));

    /* the rbtree count is now 0. */
    TEST_ASSERT(0 == rbtree_count(tree));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
