/**
 * \file test/rbtree/test_rbtree_swap.cpp
 *
 * \brief Unit tests for rbtree_swap.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/rbtree.h>
#include <rcpr/resource/protected.h>
#include <stdlib.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

TEST_SUITE(rbtree_swap);

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
 * We can swap two rbtree instances.
 */
TEST(swap_basics)
{
    allocator* alloc = nullptr;
    rbtree* left = nullptr;
    rbtree* right = nullptr;
    resource* r;
    integer* a = nullptr;
    integer* b = nullptr;
    integer* c = nullptr;
    integer* d = nullptr;
    integer* e = nullptr;
    integer* f = nullptr;
    const int akey = 1;
    const int bkey = 2;
    const int ckey = 3;
    const int dkey = 4;
    const int ekey = 5;
    const int fkey = 6;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create the left rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &left, alloc, &integer_compare, &integer_key, nullptr));

    /* we should be able to create the right rbtree instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            rbtree_create(
                &right, alloc, &integer_compare, &integer_key, nullptr));

    /* we should be able to create each integer value. */
    TEST_ASSERT(STATUS_SUCCESS == integer_create(&a, akey));
    TEST_ASSERT(STATUS_SUCCESS == integer_create(&b, bkey));
    TEST_ASSERT(STATUS_SUCCESS == integer_create(&c, ckey));
    TEST_ASSERT(STATUS_SUCCESS == integer_create(&d, dkey));
    TEST_ASSERT(STATUS_SUCCESS == integer_create(&e, ekey));
    TEST_ASSERT(STATUS_SUCCESS == integer_create(&f, fkey));

    /* insert the left tree values. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_insert(left, &a->hdr));
    TEST_ASSERT(STATUS_SUCCESS == rbtree_insert(left, &b->hdr));
    TEST_ASSERT(STATUS_SUCCESS == rbtree_insert(left, &c->hdr));

    /* insert the right tree values. */
    TEST_ASSERT(STATUS_SUCCESS == rbtree_insert(right, &d->hdr));
    TEST_ASSERT(STATUS_SUCCESS == rbtree_insert(right, &e->hdr));
    TEST_ASSERT(STATUS_SUCCESS == rbtree_insert(right, &f->hdr));

    /* PRECONDITIONS. */

    /* we should be able to find a, b, and c in the left tree. */
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, left, &akey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, left, &bkey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, left, &ckey));

    /* we should NOT be able to find d, e, and f in the left tree. */
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, left, &dkey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, left, &ekey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, left, &fkey));

    /* we should NOT be able to find a, b, and c in the right tree. */
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, right, &akey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, right, &bkey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, right, &ckey));

    /* we should be able to find d, e, and f in the right tree. */
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, right, &dkey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, right, &ekey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, right, &fkey));

    /* swap the trees. */
    rbtree_swap(left, right);

    /* POSTCONDITIONS. */

    /* we should NOT be able to find a, b, and c in the left tree. */
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, left, &akey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, left, &bkey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, left, &ckey));

    /* we should be able to find d, e, and f in the left tree. */
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, left, &dkey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, left, &ekey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, left, &fkey));

    /* we should be able to find a, b, and c in the right tree. */
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, right, &akey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, right, &bkey));
    TEST_EXPECT(STATUS_SUCCESS == rbtree_find(&r, right, &ckey));

    /* we should NOT be able to find d, e, and f in the right tree. */
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, right, &dkey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, right, &ekey));
    TEST_EXPECT(STATUS_SUCCESS != rbtree_find(&r, right, &fkey));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(left)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(rbtree_resource_handle(right)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
