/**
 * \file test/test_psock_read_write_raw_uint16.cpp
 *
 * \brief Unit tests for psock_read_raw_uint16 / psock_write_raw_uint16.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(psock_read_write_raw_uint16);

/**
 * Verify that we can read and write raw uint16 values.
 */
TEST(read_write)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const uint16_t EXPECTED_VALUE = 2983;
    uint16_t val = 0;

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

    /* we should be able to write a 16-bit unsigned integer to the lhs sock. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_uint16(ls, EXPECTED_VALUE));

    /* we should be able to read a 16-bit unsigned integer from the rhs sock. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_raw_uint16(rs, &val));

    /* the values should match. */
    TEST_EXPECT(
        EXPECTED_VALUE == val);

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
