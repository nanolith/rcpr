/**
 * \file test/test_psock_from_descriptor_setsockopt.cpp
 *
 * \brief Unit tests for psock_from_descriptor_setsockopt.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <unistd.h>

using namespace std;

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

TEST_SUITE(psock_from_descriptor_setsockopt);

/**
 * Verify that attempting to set SO_REUSEADDR succeeds.
 */
TEST(set)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    int lhs, rhs;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* create a psock from lhs. */
    TEST_ASSERT(STATUS_SUCCESS == psock_create_from_descriptor(&s, alloc, lhs));

    /* setsockopt should succeed. */
    int optval = 1;
    TEST_EXPECT(
        STATUS_SUCCESS
            == psock_setsockopt(
                    s, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof(optval)));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(s)));
    TEST_ASSERT(0 == close(rhs));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
