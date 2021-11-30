/**
 * \file test/test_psock_socket_type.cpp
 *
 * \brief Unit tests for psock_socket_type.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

TEST_SUITE(psock_socket_type);

/**
 * Verify that we get a PSOCK_SOCKET_TYPE_STREAM from a SOCK_STREAM instance.
 */
TEST(sock_stream)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int lhs;
    int rhs;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* close the rhs; we don't need it. */
    close(rhs);

    /* we should be able to create a psock from the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &s, alloc, lhs));

    /* if we get the socket type, it should be PSOCK_SOCKET_TYPE_STREAM. */
    TEST_EXPECT(PSOCK_SOCKET_TYPE_STREAM == psock_socket_type(s));

    /* we should be able to release the socket, which in turn will close the lhs
     * descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we get a PSOCK_SOCKET_TYPE_DATAGRAM from a SOCK_DGRAM instance.
 */
TEST(sock_datagram)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int lhs;
    int rhs;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(AF_UNIX, SOCK_DGRAM, 0, &lhs, &rhs));

    /* close the rhs; we don't need it. */
    close(rhs);

    /* we should be able to create a psock from the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &s, alloc, lhs));

    /* if we get the socket type, it should be PSOCK_SOCKET_TYPE_DATAGRAM. */
    TEST_EXPECT(PSOCK_SOCKET_TYPE_DATAGRAM == psock_socket_type(s));

    /* we should be able to release the socket, which in turn will close the lhs
     * descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we get a PSOCK_SOCKET_TYPE_OTHER from a buffer instance.
 */
TEST(sock_other)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const char* teststring = "this is a test.";
    size_t testsize = strlen(teststring);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the test string buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, teststring, testsize));

    /* if we get the socket type, it should be PSOCK_SOCKET_TYPE_OTHER. */
    TEST_EXPECT(PSOCK_SOCKET_TYPE_OTHER == psock_socket_type(s));

    /* we should be able to release the socket, which in turn will close the lhs
     * descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
