/**
 * \file test/test_psock_read_write_boxed_data.cpp
 *
 * \brief Unit tests for psock_read_boxed_data / psock_write_boxed_data.
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

TEST_SUITE(psock_read_write_boxed_data);

/**
 * Verify that we can read and write boxed data values.
 */
TEST(read_write_data)
{
    allocator* alloc = nullptr;
    psock* ls = nullptr;
    psock* rs = nullptr;
    int lhs;
    int rhs;
    const uint8_t EXPECTED_VALUE[] = {7, 6, 4, 1, 3 };
    uint8_t* val = nullptr;
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
            psock_write_boxed_data(ls, EXPECTED_VALUE, sizeof(EXPECTED_VALUE)));

    /* we should be able to read a 8-bit unsigned integer to the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_read_boxed_data(rs, alloc, (void**)&val, &val_size));

    /* the values should match. */
    TEST_ASSERT(sizeof(EXPECTED_VALUE) == val_size);
    TEST_ASSERT(nullptr != val);
    TEST_EXPECT(0 == memcmp(EXPECTED_VALUE, val, sizeof(EXPECTED_VALUE)));

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
    uint8_t* val = nullptr;
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
            psock_read_boxed_data(rs, alloc, (void**)&val, &val_size));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(ls)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(psock_resource_handle(rs)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
