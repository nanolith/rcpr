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
