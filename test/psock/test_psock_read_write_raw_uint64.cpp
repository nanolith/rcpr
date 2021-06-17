/**
 * \file test/test_psock_read_write_raw_uint64.cpp
 *
 * \brief Unit tests for psock_read_raw_uint64 / psock_write_raw_uint64.
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

TEST_SUITE(psock_read_write_raw_uint64);

/**
 * Verify that we can read and write raw uint64 values.
 */
TEST(read_write)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const uint64_t EXPECTED_VALUE = 128929839;
    uint64_t val = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* we should be able to create a psock from the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &ls, alloc, lhs));

    /* we should be able to create a psock from the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &rs, alloc, rhs));

    /* we should be able to write a 64-bit unsigned integer to the lhs sock. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_uint64(ls, EXPECTED_VALUE));

    /* we should be able to read a 64-bit unsigned integer from the rhs sock. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_raw_uint64(rs, &val));

    /* the values should match. */
    TEST_EXPECT(
        EXPECTED_VALUE == val);

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
