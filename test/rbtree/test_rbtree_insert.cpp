/**
 * \file test/rbtree/test_rbtree_insert.cpp
 *
 * \brief Unit tests for rbtree_insert.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/rbtree.h>
#include <stdlib.h>

#include "../../src/resource/resource_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
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
    void* context, const void* lhs, const void* rhs)
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
static const void* integer_key(void* context, const resource* r)
{
    const integer* i = (const integer*)r;

    return &i->val;
}

/**
 * Insert an integer into an empty tree.
 */
TEST(insert_empty)
{
    allocator* alloc = nullptr;
    rbtree* tree = nullptr;
    integer* value = nullptr;
    const int key = 15;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &tree, alloc, &integer_compare, &integer_key, nullptr));

    /* we should be able to create an integer value. */
    TEST_ASSERT(
        STATUS_SUCCESS == integer_create(&value, key));

    /* PRECONDITION: finding an integer returns ERROR_RBTREE_NOT_FOUND. */
    resource* x = nullptr;
    TEST_ASSERT(
        ERROR_RBTREE_NOT_FOUND == rbtree_find(&x, tree, &key));

    /* insert the value. */
    TEST_ASSERT(
        STATUS_SUCCESS == rbtree_insert(tree, &value->hdr));

    /* POSTCONDITION: we can find the integer resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == rbtree_find(&x, tree, &key));

    /* POSTCONDITION: this found value is our value. */
    TEST_EXPECT(&value->hdr == x);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Insert two integers into a list.
 */
TEST(insert_double)
{
    allocator* alloc = nullptr;
    rbtree* tree = nullptr;
    integer* value1 = nullptr;
    integer* value2 = nullptr;
    const int key1 = 15;
    const int key2 = 7;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &tree, alloc, &integer_compare, &integer_key, nullptr));

    /* we should be able to create the first integer. */
    TEST_ASSERT(
        STATUS_SUCCESS == integer_create(&value1, key1));

    /* we should be able to create the second integer. */
    TEST_ASSERT(
        STATUS_SUCCESS == integer_create(&value2, key2));

    /* PRECONDITION: finding first integer returns ERROR_RBTREE_NOT_FOUND. */
    resource* x = nullptr;
    TEST_ASSERT(
        ERROR_RBTREE_NOT_FOUND == rbtree_find(&x, tree, &key1));

    /* PRECONDITION: finding second integer returns ERROR_RBTREE_NOT_FOUND. */
    TEST_ASSERT(
        ERROR_RBTREE_NOT_FOUND == rbtree_find(&x, tree, &key2));

    /* insert the first integer. */
    TEST_ASSERT(
        STATUS_SUCCESS == rbtree_insert(tree, &value1->hdr));

    /* insert the second integer. */
    TEST_ASSERT(
        STATUS_SUCCESS == rbtree_insert(tree, &value2->hdr));

    /* POSTCONDITION: we can find the first integer resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == rbtree_find(&x, tree, &key1));

    /* POSTCONDITION: this found value is our first value. */
    TEST_EXPECT(&value1->hdr == x);

    /* POSTCONDITION: we can find the second integer resource. */
    TEST_ASSERT(
        STATUS_SUCCESS == rbtree_find(&x, tree, &key2));

    /* POSTCONDITION: this found value is our second value. */
    TEST_EXPECT(&value2->hdr == x);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(tree)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
