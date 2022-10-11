/**
 * \file test/test_psock_br_read_line.cpp
 *
 * \brief Unit tests for psock_br_read_line.
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

TEST_SUITE(psock_br_read_line);

/**
 * Verify that we can read a line that ends in EOF.
 */
TEST(basics_eof)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock_br* br = nullptr;
    const char* buffer = "this is a test.";
    size_t buffer_size = strlen(buffer);
    char line_buffer[1024];
    size_t line_buffer_size = sizeof(line_buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to read a line. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* the line buffer should be what we expect. */
    TEST_EXPECT(0 == strcmp(line_buffer, buffer));

    /* we should be able to release the br instance. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_br_resource_handle(br)));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can read the first line of an input buffer.
 */
TEST(first_line)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock_br* br = nullptr;
    const char* buffer = "first line\nsecond line.";
    size_t buffer_size = strlen(buffer);
    char line_buffer[1024];
    size_t line_buffer_size = sizeof(line_buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to read a line. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* the line buffer should be what we expect. */
    TEST_EXPECT(0 == strcmp(line_buffer, "first line"));

    /* we should be able to release the br instance. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_br_resource_handle(br)));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can read the second line of an input buffer.
 */
TEST(second_line)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock_br* br = nullptr;
    const char* buffer = "first line\nsecond line.";
    size_t buffer_size = strlen(buffer);
    char line_buffer[1024];
    size_t line_buffer_size = sizeof(line_buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to read the first line. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* we should be able to read the second line. */
    line_buffer_size = sizeof(line_buffer);
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* the line buffer should be what we expect. */
    TEST_EXPECT(0 == strcmp(line_buffer, "second line."));

    /* we should be able to release the br instance. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_br_resource_handle(br)));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that a line is truncated when too large.
 */
TEST(line_truncated)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock_br* br = nullptr;
    const char* buffer = "test line 1234.";
    size_t buffer_size = strlen(buffer);
    char line_buffer[1024];
    size_t line_buffer_size = sizeof(line_buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* force the first line to be truncated. */
    line_buffer_size = 5;

    /* the line should get a truncation error. */
    TEST_ASSERT(
        ERROR_PSOCK_BR_READ_LINE_TRUNCATED
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* the line size should be 4. */
    TEST_EXPECT(4 == line_buffer_size);

    /* the line should have the first four characters in it. */
    TEST_EXPECT(0 == strcmp(line_buffer, "test"));

    /* we should be able to read the second line. */
    line_buffer_size = sizeof(line_buffer);
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* the line buffer should contain the rest of the line. */
    TEST_EXPECT(0 == strcmp(line_buffer, " line 1234."));

    /* we should be able to release the br instance. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_br_resource_handle(br)));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can handle an extra long line.
 */
TEST(extra_long_line)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock_br* br = nullptr;
    char buffer[65536];
    size_t buffer_size = sizeof(buffer) - 1;
    char line_buffer[65537];
    size_t line_buffer_size = sizeof(line_buffer);

    /* set the buffer data. */
    memset(buffer, 'a', buffer_size);
    buffer[buffer_size] = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* read an extra long line, forcing the internal buffer to be refilled. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == psock_br_read_line(line_buffer, &line_buffer_size, br));

    /* the line buffer should contain the buffer contents. */
    TEST_EXPECT(0 == strcmp(line_buffer, buffer));

    /* we should be able to release the br instance. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_br_resource_handle(br)));

    /* we should be able to release the socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(s)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
