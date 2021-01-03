/**
 * \file test/test_socket_utility_hton16.cpp
 *
 * \brief Unit tests for malloc allocator.
 */

#include <minunit/minunit.h>
#include <rcpr/socket_utilities.h>

TEST_SUITE(socket_utility_hton16);

/**
 * Verify that hton16 works.
 */
TEST(basics)
{
#ifdef __BIG_ENDIAN__
    int16_t EXPECTED_NETWORK_VALUE      = 0x1234;

    /* this maintains host / network order. */
    TEST_EXPECT(
        EXPECTED_NETWORK_VALUE ==
            socket_utility_hton16(EXPECTED_NETWORK_VALUE));

#else
    int16_t EXPECTED_HOST_VALUE         = 0x3412;
    int16_t EXPECTED_NETWORK_VALUE      = 0x1234;

    /* this converts to network order. */
    TEST_EXPECT(
        EXPECTED_NETWORK_VALUE ==
            socket_utility_hton16(EXPECTED_HOST_VALUE));

    /* doing the conversion twice undoes it. */
    TEST_EXPECT(
        EXPECTED_HOST_VALUE ==
            socket_utility_hton16(
                socket_utility_hton16(EXPECTED_HOST_VALUE)));
#endif
}
