/**
 * \file test/test_psock_from_buffer_write.cpp
 *
 * \brief Unit tests for psock_from_buffer_write.
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

TEST_SUITE(psock_from_buffer_write);

/**
 * Verify that we can write data to a psock backed by a buffer and get the
 * buffer back.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const char* EXPECTED_BUFFER = "TEST";
    size_t EXPECTED_BUFFER_SIZE = strlen(EXPECTED_BUFFER) + 1;
    char* output_buffer = nullptr;
    size_t output_buffer_size = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an output buffer psock instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, NULL, 0));

    /* we can write the expected buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_data(s, EXPECTED_BUFFER, EXPECTED_BUFFER_SIZE));

    /* we can get the output buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_from_buffer_get_output_buffer(
                s, alloc, (void**)&output_buffer, &output_buffer_size));
    TEST_ASSERT(nullptr != output_buffer);
    TEST_ASSERT(EXPECTED_BUFFER_SIZE == output_buffer_size);
    TEST_EXPECT(
        0 == memcmp(output_buffer, EXPECTED_BUFFER, EXPECTED_BUFFER_SIZE));

    /* clean up the allocated memory for the output buffer. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, output_buffer));

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
 * Verify that we can write 5000 bytes to an output buffer.
 */
TEST(five_k)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    char* input_buffer;
    size_t input_buffer_size = 5000;
    char* output_buffer = nullptr;
    size_t output_buffer_size = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an input buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_allocate(
                alloc, (void**)&input_buffer, input_buffer_size));

    /* set the data in this buffer. */
    memset(input_buffer, 'a', input_buffer_size);

    /* we should be able to create an output buffer psock instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, NULL, 0));

    /* we can write the expected buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_data(s, input_buffer, input_buffer_size));

    /* we can get the output buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_from_buffer_get_output_buffer(
                s, alloc, (void**)&output_buffer, &output_buffer_size));
    TEST_ASSERT(nullptr != output_buffer);
    TEST_ASSERT(input_buffer_size == output_buffer_size);
    TEST_EXPECT(
        0 == memcmp(output_buffer, input_buffer, input_buffer_size));

    /* clean up the allocated memory for the input buffer. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, input_buffer));

    /* clean up the allocated memory for the output buffer. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, output_buffer));

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
 * Verify that we can write 16k bytes to an output buffer.
 */
TEST(sixteen_k)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    char* input_buffer;
    size_t input_buffer_size = 16384;
    char* output_buffer = nullptr;
    size_t output_buffer_size = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an input buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            allocator_allocate(
                alloc, (void**)&input_buffer, input_buffer_size));

    /* set the data in this buffer. */
    memset(input_buffer, 'a', input_buffer_size);

    /* we should be able to create an output buffer psock instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, NULL, 0));

    /* we can write the expected buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_write_raw_data(s, input_buffer, input_buffer_size));

    /* we can get the output buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_from_buffer_get_output_buffer(
                s, alloc, (void**)&output_buffer, &output_buffer_size));
    TEST_ASSERT(nullptr != output_buffer);
    TEST_ASSERT(input_buffer_size == output_buffer_size);
    TEST_EXPECT(
        0 == memcmp(output_buffer, input_buffer, input_buffer_size));

    /* clean up the allocated memory for the input buffer. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, input_buffer));

    /* clean up the allocated memory for the output buffer. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, output_buffer));

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
 * Verify that we get an error when attempting to write to a read psock buffer.
 */
TEST(bad_write_input_stream)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    const char* foo = "foo bar";
    size_t foo_size = strlen(foo) + 1;
    char* output_buffer = nullptr;
    size_t output_buffer_size = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an input buffer psock instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(
                &s, alloc, foo, foo_size));

    /* It's an error to write to this buffer. */
    TEST_EXPECT(
        ERROR_PSOCK_UNSUPPORTED_TYPE ==
            psock_write_raw_data(s, foo, foo_size));

    /* it is an error to try to get the output buffer for this psock. */
    TEST_EXPECT(
        ERROR_PSOCK_UNSUPPORTED_TYPE ==
            psock_from_buffer_get_output_buffer(
                s, alloc, (void**)&output_buffer, &output_buffer_size));

    /* we should be able to release the socket, which in turn will close the lhs
     * descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
