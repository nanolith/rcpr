/**
 * \file test/test_psock_read_write_boxed_bool.cpp
 *
 * \brief Unit tests for psock_read_boxed_bool / psock_write_boxed_bool.
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

TEST_SUITE(psock_read_write_boxed_bool);

/**
 * Verify that we can read and write boxed bool values.
 */
TEST(read_write_true)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const bool EXPECTED_VALUE = true;
    bool val = false;

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

    /* we should be able to write a 8-bit unsigned integer to the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_boxed_bool(ls, EXPECTED_VALUE));

    /* we should be able to read a 8-bit unsigned integer to the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_boxed_bool(rs, &val));

    /* the values should match. */
    TEST_EXPECT(
        EXPECTED_VALUE == val);

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can read and write boxed bool values.
 */
TEST(read_write_false)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const bool EXPECTED_VALUE = false;
    bool val = true;

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

    /* we should be able to write a 8-bit unsigned integer to the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_boxed_bool(ls, EXPECTED_VALUE));

    /* we should be able to read a 8-bit unsigned integer to the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_boxed_bool(rs, &val));

    /* the values should match. */
    TEST_EXPECT(
        EXPECTED_VALUE == val);

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that if we write an invalid boxed value, we'll get an error when
 * reading.
 */
TEST(write_invalid_read_error)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    bool val = false;

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

    /* write a bad type. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_uint32(ls, PSOCK_BOXED_TYPE_INT32));

    /* write a raw bool value. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_int32(ls, 7));

    /* reading a boxed bool value should fail. */
    TEST_ASSERT(
        ERROR_PSOCK_READ_BOXED_INVALID_TYPE ==
            psock_read_boxed_bool(rs, &val));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
