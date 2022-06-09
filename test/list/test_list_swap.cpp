/**
 * \file test/test_list_swap.cpp
 *
 * \brief Unit tests for list_swap.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/resource/protected.h>
#include <rcpr/list.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_list;

TEST_SUITE(slist_swap);

typedef struct intval intval;
struct intval
{
    resource hdr;
    allocator* alloc;
    int val;
};

static status intval_resource_release(resource* r)
{
    intval* v = (intval*)r;

    /* cache allocator. */
    allocator* alloc = v->alloc;

    /* reclaim memory. */
    return
        allocator_reclaim(alloc, v);
}

static status intval_create(intval** v, allocator* alloc, int val)
{
    status retval;
    intval* tmp = nullptr;

    /* allocate structure. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(*tmp));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* initialize resource. */
    resource_init(&tmp->hdr, &intval_resource_release);

    /* set values. */
    tmp->alloc = alloc;
    tmp->val = val;

    /* success. */
    *v = tmp;
    return STATUS_SUCCESS;
}

/**
 * Verify that we can swap two lists.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    list* left = nullptr;
    list* right = nullptr;
    intval* a = nullptr;
    intval* b = nullptr;
    intval* c = nullptr;
    intval* d = nullptr;
    intval* e = nullptr;
    intval* f = nullptr;
    list_node* x;
    resource* r;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create the left list. */
    TEST_ASSERT(
        STATUS_SUCCESS == list_create(&left, alloc));

    /* we should be able to create the right list. */
    TEST_ASSERT(
        STATUS_SUCCESS == list_create(&right, alloc));

    /* create each intval. */
    TEST_ASSERT(STATUS_SUCCESS == intval_create(&a, alloc, 1));
    TEST_ASSERT(STATUS_SUCCESS == intval_create(&b, alloc, 2));
    TEST_ASSERT(STATUS_SUCCESS == intval_create(&c, alloc, 3));
    TEST_ASSERT(STATUS_SUCCESS == intval_create(&d, alloc, 4));
    TEST_ASSERT(STATUS_SUCCESS == intval_create(&e, alloc, 5));
    TEST_ASSERT(STATUS_SUCCESS == intval_create(&f, alloc, 6));

    /* append abc into left. */
    TEST_ASSERT(STATUS_SUCCESS == list_append_tail(left, &a->hdr));
    TEST_ASSERT(STATUS_SUCCESS == list_append_tail(left, &b->hdr));
    TEST_ASSERT(STATUS_SUCCESS == list_append_tail(left, &c->hdr));

    /* append def into right. */
    TEST_ASSERT(STATUS_SUCCESS == list_append_tail(right, &d->hdr));
    TEST_ASSERT(STATUS_SUCCESS == list_append_tail(right, &e->hdr));
    TEST_ASSERT(STATUS_SUCCESS == list_append_tail(right, &f->hdr));

    /* swap left and right. */
    list_swap(left, right);

    /* check that left head's resource is d. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&x, left));
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r, x));
    TEST_EXPECT(r == &d->hdr);

    /* check that left tail's resource is f. */
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&x, left));
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r, x));
    TEST_EXPECT(r == &f->hdr);

    /* check that right head's resource is a. */
    TEST_ASSERT(STATUS_SUCCESS == list_head(&x, right));
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r, x));
    TEST_EXPECT(r == &a->hdr);

    /* check that right tail's resource is c. */
    TEST_ASSERT(STATUS_SUCCESS == list_tail(&x, right));
    TEST_ASSERT(STATUS_SUCCESS == list_node_child(&r, x));
    TEST_EXPECT(r == &c->hdr);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(list_resource_handle(left)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(list_resource_handle(right)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
