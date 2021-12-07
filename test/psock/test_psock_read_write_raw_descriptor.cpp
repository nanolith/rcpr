/**
 * \file test/test_psock_read_write_raw_descriptor.cpp
 *
 * \brief Unit tests for psock_read_raw_descriptor and
 * psock_write_raw_descriptor.
 */

#include <fcntl.h>
#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

TEST_SUITE(psock_read_write_raw_descriptor);

static size_t count_open_fds()
{
    status retval;
    struct rlimit rl;
    size_t open_files = 0;

    retval = getrlimit(RLIMIT_NOFILE, &rl);
    if (retval < 0)
    {
        perror("getrlimit");
        exit(1);
    }

    for (size_t i = 0; i < rl.rlim_max; ++i)
    {
        retval = fcntl(i, F_GETFL);
        if (retval < 0)
            continue;

        ++open_files;
    }

    return open_files;
}

/**
 * Verify that attempting to write a raw descriptor to a stream socket fails.
 */
TEST(write_raw_descriptor_stream)
{
    allocator* alloc = nullptr;
    psock* sl = nullptr;
    psock* sr = nullptr;
    int lhs;
    int rhs;

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
                &sl, alloc, lhs));

    /* we should be able to create a psock from the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sr, alloc, rhs));

    /* writing a descriptor to the lhs socket should fail. */
    TEST_ASSERT(
        ERROR_PSOCK_UNSUPPORTED_TYPE ==
            psock_write_raw_descriptor(sl, rhs));

    /* release the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(sl)));

    /* release the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(sr)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that attempting to read a raw descriptor from a stream socket fails.
 */
TEST(read_raw_descriptor_stream)
{
    allocator* alloc = nullptr;
    psock* sl = nullptr;
    psock* sr = nullptr;
    int lhs;
    int rhs;
    int desc;

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
                &sl, alloc, lhs));

    /* we should be able to create a psock from the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sr, alloc, rhs));

    /* reading a descriptor from the rhs socket should fail. */
    TEST_ASSERT(
        ERROR_PSOCK_UNSUPPORTED_TYPE ==
            psock_read_raw_descriptor(
                sr, &desc));

    /* release the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sl)));

    /* release the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sr)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can pass a descriptor through a datagram socket.
 */
TEST(read_write_raw_descriptor_datagram)
{
    allocator* alloc = nullptr;
    psock* sl = nullptr;
    psock* sr = nullptr;
    int lhs, lhs_dg;
    int rhs, rhs_dg;
    int desc;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* get the open file count. */
    size_t open_files1 = count_open_fds();

    /* we should be able to create socket pairs. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_DGRAM, 0, &lhs_dg, &rhs_dg));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* the number of open files should have increased by 4. */
    size_t open_files2 = count_open_fds();
    TEST_ASSERT(open_files1 + 4 == open_files2);

    /* create a psock from the lhs_dg socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sl, alloc, lhs_dg));

    /* create a psock from the rhs_dg socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sr, alloc, rhs_dg));

    /* write the rhs descriptor to the sl socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_write_raw_descriptor(sl, rhs));

    /* the SCM_RIGHTS packet does not increase the number of open files. */
    size_t open_files3 = count_open_fds();
    TEST_ASSERT(open_files2 == open_files3);

    /* read the rhs descriptor from the sr socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_read_raw_descriptor(sr, &desc));

    /* reading the SCM_RIGHTS packet increases the number of open files by 1. */
    size_t open_files4 = count_open_fds();
    TEST_ASSERT(open_files3 + 1 == open_files4);

    /* verify that desc is a valid socket. */
    TEST_EXPECT(desc >= 0);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sl)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sr)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
    close(lhs);
    close(rhs);
    close(desc);
}
