/**
 * \file test/test_socket_utility_socketpair.cpp
 *
 * \brief Unit tests for socket_utility_socketpair.
 */

#include <minunit/minunit.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <unistd.h>

TEST_SUITE(socket_utility_socketpair);

/**
 * Verify that we can create a socket pair and read / write to / from it.
 */
TEST(create)
{
    int lhs;
    int rhs;
    const int EXPECTED_VALUE = 778;
    int read_value = 0;

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* we should be able to write to one end of the socket pair. */
    TEST_ASSERT(
        sizeof(int) == write(lhs, &EXPECTED_VALUE, sizeof(int)));

    /* we should be able to read from the other end of the socket pair. */
    TEST_ASSERT(
        sizeof(int) == read(rhs, &read_value, sizeof(int)));

    /* the value should have been read correctly. */
    TEST_EXPECT(
        EXPECTED_VALUE == read_value);

    /* clean up. */
    close(lhs);
    close(rhs);
}
