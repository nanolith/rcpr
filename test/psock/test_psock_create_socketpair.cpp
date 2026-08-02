/**
 * \file test/test_psock_create_socketpair.cpp
 *
 * \brief Unit tests for psock_create_socketpair.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

TEST_SUITE(psock_create_socketpair);

/**
 * Verify that we can create and release socketpair psock instances.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    psock* lhs = nullptr;
    psock* rhs = nullptr;
    const uint64_t TEST_VAL = 192;
    uint64_t recv_val = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_create_socketpair(
                    &lhs, &rhs, alloc, AF_UNIX, SOCK_STREAM, 0));

    /* verify that these sockets have been created. */
    TEST_ASSERT(nullptr != lhs);
    TEST_ASSERT(nullptr != rhs);

    /* write a uint64_t to lhs. */
    TEST_ASSERT(STATUS_SUCCESS == psock_write_boxed_uint64(lhs, TEST_VAL));

    /* read this uint64_t from rhs. */
    TEST_ASSERT(STATUS_SUCCESS == psock_read_boxed_uint64(rhs, &recv_val));

    /* the two values should match. */
    TEST_EXPECT(TEST_VAL == recv_val);

    /* clean up */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(lhs)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rhs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
