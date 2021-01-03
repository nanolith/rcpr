/**
 * \file test/test_socket_utility_ntoh64.cpp
 *
 * \brief Unit tests for malloc allocator.
 */

#include <minunit/minunit.h>
#include <rcpr/socket_utilities.h>

TEST_SUITE(socket_utility_ntoh64);

/**
 * Verify that ntoh64 works.
 */
TEST(basics)
{
#ifdef __BIG_ENDIAN__
    int64_t EXPECTED_NETWORK_VALUE      = 0x123456789ABCDEF0;

    /* this maintains host / network order. */
    TEST_EXPECT(
        EXPECTED_NETWORK_VALUE ==
            socket_utility_ntoh64(EXPECTED_NETWORK_VALUE));

#else
    int64_t EXPECTED_HOST_VALUE         = 0xF0DEBC9A78563412;
    int64_t EXPECTED_NETWORK_VALUE      = 0x123456789ABCDEF0;

    /* this converts to network order. */
    TEST_EXPECT(
        EXPECTED_HOST_VALUE ==
            socket_utility_ntoh64(EXPECTED_NETWORK_VALUE));

    /* doing the conversion twice undoes it. */
    TEST_EXPECT(
        EXPECTED_NETWORK_VALUE ==
            socket_utility_ntoh64(
                socket_utility_ntoh64(EXPECTED_NETWORK_VALUE)));
#endif
}
