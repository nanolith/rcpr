/**
 * \file test/test_psock_from_buffer_read.cpp
 *
 * \brief Unit tests for psock_from_buffer_read.
 */

#include <cstring>
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

TEST_SUITE(psock_from_buffer_read);

/**
 * Verify that we can read data from a psock created from a buffer.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const char* buffer = "TEST";
    size_t buffer_size = strlen(buffer);
    char read_buffer[1];
    size_t read_size;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, buffer, buffer_size));

    /* we can read a T. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw(s, &read_buffer, &read_size));
    TEST_ASSERT(1U == read_size);
    TEST_EXPECT('T' == read_buffer[0]);

    /* we can read an E. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw(s, &read_buffer, &read_size));
    TEST_ASSERT(1U == read_size);
    TEST_EXPECT('E' == read_buffer[0]);

    /* we can read an S. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw(s, &read_buffer, &read_size));
    TEST_ASSERT(1U == read_size);
    TEST_EXPECT('S' == read_buffer[0]);

    /* we can read a T. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw(s, &read_buffer, &read_size));
    TEST_ASSERT(1U == read_size);
    TEST_EXPECT('T' == read_buffer[0]);

    /* The last read ends in EOF. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(
        ERROR_PSOCK_READ_EOF == psock_read_raw(s, &read_buffer, &read_size));

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
 * Reading more data than available results in a success with an adjusted size.
 */
TEST(overread)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const char* buffer = "TEST";
    size_t buffer_size = strlen(buffer);
    char read_buffer[100];
    size_t read_size;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, buffer, buffer_size));

    /* we can read a T. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw(s, &read_buffer, &read_size));
    TEST_ASSERT(4U == read_size);
    TEST_EXPECT(0 == memcmp(buffer, read_buffer, 4U));

    /* The last read ends in EOF. */
    read_size = sizeof(read_buffer);
    TEST_ASSERT(
        ERROR_PSOCK_READ_EOF == psock_read_raw(s, &read_buffer, &read_size));

    /* we should be able to release the socket, which in turn will close the lhs
     * descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
