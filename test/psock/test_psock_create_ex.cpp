/**
 * \file test/test_psock_create_ex.cpp
 *
 * \brief Unit tests for psock_create_ex.
 */

#include <minunit/minunit.h>
#include <netinet/in.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

TEST_SUITE(psock_create_ex);

/**
 * Verify that we can create and release a psock instance created from user
 * functions.
 */
TEST(create_simple)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr, nullptr, nullptr, nullptr, nullptr));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If read is undefined, then calling psock_read returns an undefined user
 * function error.
 */
TEST(psock_read_null)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int32_t val;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr, nullptr, nullptr, nullptr, nullptr));

    /* psock_read should return an undefined error. */
    TEST_EXPECT(
        ERROR_PSOCK_USER_METHOD_UNDEFINED ==
            psock_read_boxed_int32(
                s, &val));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If read is defined, then calling psock_read returns the return code from
 * the user function.
 */
TEST(psock_read_custom)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int32_t val;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr,
                [](psock*, void*, void*, size_t*, bool) {
                    return -3;
                },
                nullptr, nullptr, nullptr));

    /* psock_read should return the above value from the lambda. */
    TEST_EXPECT(
        -3 ==
            psock_read_boxed_int32(
                s, &val));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If write is undefined, then calling psock_write returns an undefined user
 * function error.
 */
TEST(psock_write_null)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const int32_t val = 17;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr, nullptr, nullptr, nullptr, nullptr));

    /* psock_write should return an undefined error. */
    TEST_EXPECT(
        ERROR_PSOCK_USER_METHOD_UNDEFINED ==
            psock_write_boxed_int32(
                s, val));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If write is defined, then calling psock_write returns the return code from
 * the user function.
 */
TEST(psock_write_custom)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const int32_t val = 17;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr, nullptr,
                [](psock*, void*, const void*, size_t*) {
                    return -3;
                },
                nullptr, nullptr));

    /* psock_write should return the above value from the lambda. */
    TEST_EXPECT(
        -3 ==
            psock_write_boxed_int32(
                s, val));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If accept is undefined, then calling psock_accept returns an undefined user
 * function error.
 */
TEST(psock_accept_null)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int desc;
    struct sockaddr_in addr;
    socklen_t addr_size = sizeof(addr);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr, nullptr, nullptr, nullptr, nullptr));

    /* psock_accept should return an undefined error. */
    TEST_EXPECT(
        ERROR_PSOCK_USER_METHOD_UNDEFINED ==
            psock_accept(
                s, &desc, (struct sockaddr*)&addr, &addr_size));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If accept is defined, then calling psock_accept returns the return code from
 * the user function.
 */
TEST(psock_accept_custom)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int desc;
    struct sockaddr_in addr;
    socklen_t addr_size = sizeof(addr);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, nullptr, nullptr, nullptr,
                [](psock*, void*, int*, struct sockaddr*, socklen_t*) {
                    return -3;
                },
                nullptr));

    /* psock_accept should the error code from the above lambda function. */
    TEST_EXPECT(
        -3 ==
            psock_accept(
                s, &desc, (struct sockaddr*)&addr, &addr_size));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * If release is defined, then calling resource_release on a user psock instance
 * calls this release method.
 */
TEST(psock_release_custom)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    typedef struct testfoo testfoo;
    struct testfoo
    {
        bool called;
    } bar;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* PRECONDITION: called is false. */
    bar.called = false;

    /* we should be able to create a psock from NULL functions. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_ex(
                &s, alloc, &bar, nullptr, nullptr, nullptr,
                [](psock*, void* ctx) {
                    testfoo* bar = (testfoo*)ctx;
                    bar->called = true;
                    return STATUS_SUCCESS;
                }));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* the custom release method was called, which set the called flag. */
    TEST_EXPECT(bar.called);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
