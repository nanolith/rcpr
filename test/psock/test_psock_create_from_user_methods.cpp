/**
 * \file test/test_psock_create_from_user_methods.cpp
 *
 * \brief Unit tests for psock_create_from_user_methods.
 */

#include <cstring>
#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>
#include <rcpr/vtable.h>
#include <sys/socket.h>
#include <unistd.h>

using namespace std;

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;

TEST_SUITE(psock_create_from_user_methods);

struct test_psock_context
{
    bool release_called = false;
};

static status test_psock_release(psock* sock, void* ctx);

RCPR_VTABLE
psock_vtable test_psock_vtable = {
    .hdr = { NULL },
    .read_fn = NULL,
    .write_fn = NULL,
    .accept_fn = NULL,
    .sendmsg_fn = NULL,
    .recvmsg_fn = NULL,
    .release_fn = &test_psock_release,
};

static status test_psock_release(psock* sock, void* ctx)
{
    (void)sock;

    test_psock_context* test_context = (test_psock_context*)ctx;

    test_context->release_called = true;

    return STATUS_SUCCESS;
}

/**
 * Verify that we can create and release a psock instance created from user
 * methods.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    test_psock_context ctx;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from user methods. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_user_methods(
                &s, alloc, &ctx, &test_psock_vtable));

    /* we should be able to release the socket, which in turn will call our
     * custom release method. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* the release method should have been called. */
    TEST_EXPECT(ctx.release_called);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
