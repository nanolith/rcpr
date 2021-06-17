/**
 * \file test/test_psock_read_write_raw_int16.cpp
 *
 * \brief Unit tests for psock_read_raw_int16 / psock_write_raw_int16.
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

TEST_SUITE(psock_read_write_raw_int16);

/**
 * Verify that we can read and write raw int16 values.
 */
TEST(read_write)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const int16_t EXPECTED_VALUE = 2983;
    int16_t val = 0;

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

    /* we should be able to write a 16-bit integer to the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_int16(ls, EXPECTED_VALUE));

    /* we should be able to read a 16-bit integer to the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_raw_int16(rs, &val));

    /* the values should match. */
    TEST_EXPECT(
        EXPECTED_VALUE == val);

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
