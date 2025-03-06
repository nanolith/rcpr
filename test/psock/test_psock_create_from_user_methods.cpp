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
    bool read_called = false;
    bool write_called = false;
    bool accept_called = false;
};

static status test_psock_release(psock* sock, void* ctx);
static status test_psock_read(
    psock* sock, void* ctx, void* data, size_t* size, bool block);
static status test_psock_write(
    psock* sock, void* ctx, const void* data, size_t* size);
static status test_psock_accept(
    psock* sock, void* ctx, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);

RCPR_VTABLE
psock_vtable test_psock_vtable = {
    .hdr = { NULL },
    .read_fn = &test_psock_read,
    .write_fn = &test_psock_write,
    .accept_fn = &test_psock_accept,
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

static status test_psock_read(
    psock* sock, void* ctx, void* data, size_t* size, bool block)
{
    (void)sock;
    (void)data;
    (void)size;
    (void)block;

    test_psock_context* test_context = (test_psock_context*)ctx;

    test_context->read_called = true;

    return STATUS_SUCCESS;
}

static status test_psock_write(
    psock* sock, void* ctx, const void* data, size_t* size)
{
    (void)sock;
    (void)data;
    (void)size;

    test_psock_context* test_context = (test_psock_context*)ctx;

    test_context->write_called = true;

    return STATUS_SUCCESS;
}

static status test_psock_accept(
    psock* sock, void* ctx, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    (void)sock;

    test_psock_context* test_context = (test_psock_context*)ctx;

    *desc = 0;
    memset(addr, 0, *addrlen);
    *addrlen = 0;

    test_context->accept_called = true;

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

/**
 * Verify that we can read from a user method psock.
 */
TEST(read)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    test_psock_context ctx;
    int32_t data;
    size_t data_size = sizeof(data);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from user methods. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_user_methods(
                &s, alloc, &ctx, &test_psock_vtable));

    /* we should be able to read from the psock. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_read_raw(s, &data, &data_size));

    /* this calls our function. */
    TEST_EXPECT(ctx.read_called);

    /* we should be able to release the socket, which in turn will call our
     * custom release method. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can write to a user method psock.
 */
TEST(write)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    test_psock_context ctx;
    int32_t data = 77;
    size_t data_size = sizeof(data);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from user methods. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_user_methods(
                &s, alloc, &ctx, &test_psock_vtable));

    /* we should be able to write to the psock. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_write_raw_data(s, &data, data_size));

    /* this calls our function. */
    TEST_EXPECT(ctx.write_called);

    /* we should be able to release the socket, which in turn will call our
     * custom release method. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can accept socket descriptors from a user method psock.
 */
TEST(accept)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    test_psock_context ctx;
    int desc;
    struct sockaddr addr;
    socklen_t addrlen = sizeof(addr);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from user methods. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_user_methods(
                &s, alloc, &ctx, &test_psock_vtable));

    /* we should be able to accept a socket from the the psock. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_accept(s, &desc, &addr, &addrlen));

    /* this calls our function. */
    TEST_EXPECT(ctx.accept_called);

    /* we should be able to release the socket, which in turn will call our
     * custom release method. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
