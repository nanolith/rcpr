/**
 * \file test/test_psock_read_write_boxed_string.cpp
 *
 * \brief Unit tests for psock_read_boxed_string / psock_write_boxed_string.
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

TEST_SUITE(psock_read_write_boxed_string);

/**
 * Verify that we can read and write boxed string values.
 */
TEST(read_write_string)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const char* EXPECTED_VALUE = "This is a test.";
    char* val = nullptr;
    size_t val_size = 0U;

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
            psock_write_boxed_string(ls, EXPECTED_VALUE));

    /* we should be able to read a 8-bit unsigned integer to the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_boxed_string(rs, alloc, &val, &val_size));

    /* the values should match. */
    TEST_ASSERT(strlen(EXPECTED_VALUE) == val_size);
    TEST_ASSERT(nullptr != val);
    TEST_EXPECT(0 == strcmp(EXPECTED_VALUE, val));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, val));
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
    char* val = nullptr;
    size_t val_size = 0U;

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
            psock_write_raw_uint32(ls, PSOCK_BOXED_TYPE_BOOL));

    /* write a raw bool value. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_bool(ls, false));

    /* reading a boxed uint16 value should fail. */
    TEST_ASSERT(
        ERROR_PSOCK_READ_BOXED_INVALID_TYPE ==
            psock_read_boxed_string(rs, alloc, &val, &val_size));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
