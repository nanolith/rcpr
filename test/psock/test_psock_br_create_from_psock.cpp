/**
 * \file test/test_psock_br_create_from_psock.cpp
 *
 * \brief Unit tests for psock_br_create_from_psock.
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

TEST_SUITE(psock_br_create_from_psock);

/**
 * Verify that we can create and release a psock_br instance created from a
 * psock.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock_br* br = nullptr;
    const char* buffer = "this is a test.";
    size_t buffer_size = strlen(buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

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
 * Verify that we can get the psock adapter from a psock_br instance.
 */
TEST(psock_adapter)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock* adapter = nullptr;
    psock_br* br = nullptr;
    const char* buffer = "this is a test.";
    size_t buffer_size = strlen(buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to get the psock br psock adapter instance. */
    adapter = psock_br_psock_adapter(br);
    TEST_ASSERT(nullptr != adapter);

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
 * Verify that we can read a raw character.
 */
TEST(psock_read_raw_uint8_base)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock* adapter = nullptr;
    psock_br* br = nullptr;
    uint8_t ch;
    const char* buffer = "t";
    size_t buffer_size = strlen(buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to get the psock br psock adapter instance. */
    adapter = psock_br_psock_adapter(br);
    TEST_ASSERT(nullptr != adapter);

    /* we should be able to read a character. */
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw_uint8(adapter, &ch));

    /* the character should match. */
    TEST_EXPECT((char)ch == 't');

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
 * Verify that we can read multiple raw characters.
 */
TEST(psock_read_raw_uint8_multiple)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock* adapter = nullptr;
    psock_br* br = nullptr;
    uint8_t ch;
    const char* buffer = "test";
    size_t buffer_size = strlen(buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to get the psock br psock adapter instance. */
    adapter = psock_br_psock_adapter(br);
    TEST_ASSERT(nullptr != adapter);

    /* we should be able to read a character. */
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw_uint8(adapter, &ch));

    /* the character should match. */
    TEST_EXPECT((char)ch == 't');

    /* we should be able to read a character. */
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw_uint8(adapter, &ch));

    /* the character should match. */
    TEST_EXPECT((char)ch == 'e');

    /* we should be able to read a character. */
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw_uint8(adapter, &ch));

    /* the character should match. */
    TEST_EXPECT((char)ch == 's');

    /* we should be able to read a character. */
    TEST_ASSERT(STATUS_SUCCESS == psock_read_raw_uint8(adapter, &ch));

    /* the character should match. */
    TEST_EXPECT((char)ch == 't');

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
 * Verify that reading a raw character fails with EOF when the string is empty.
 */
TEST(psock_read_raw_uint8_fail_eof)
{
    allocator* alloc = nullptr;
    psock* s = nullptr;
    psock* adapter = nullptr;
    psock_br* br = nullptr;
    uint8_t ch;
    const char* buffer = "";
    size_t buffer_size = strlen(buffer);

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a psock from the buffer. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_buffer(&s, alloc, buffer, buffer_size));

    /* we should be able to create a psock_br instance from this psock. */
    TEST_ASSERT(STATUS_SUCCESS == psock_br_create_from_psock(&br, alloc, s));

    /* we should be able to get the psock br psock adapter instance. */
    adapter = psock_br_psock_adapter(br);
    TEST_ASSERT(nullptr != adapter);

    /* attempting to read a character should fail. */
    TEST_ASSERT(ERROR_PSOCK_READ_EOF == psock_read_raw_uint8(adapter, &ch));

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
