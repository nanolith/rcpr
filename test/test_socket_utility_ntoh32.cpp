/**
 * \file test/test_socket_utility_ntoh32.cpp
 *
 * \brief Unit tests for malloc allocator.
 */

#include <minunit/minunit.h>
#include <rcpr/socket_utilities.h>

TEST_SUITE(socket_utility_ntoh32);

/**
 * Verify that ntoh32 works.
 */
TEST(basics)
{
#ifdef __BIG_ENDIAN__
    int32_t EXPECTED_NETWORK_VALUE      = 0x12345678;

    /* this maintains host / network order. */
    TEST_EXPECT(
        EXPECTED_NETWORK_VALUE ==
            socket_utility_ntoh32(EXPECTED_NETWORK_VALUE));

#else
    int32_t EXPECTED_HOST_VALUE         = 0x78563412;
    int32_t EXPECTED_NETWORK_VALUE      = 0x12345678;

    /* this converts to network order. */
    TEST_EXPECT(
        EXPECTED_HOST_VALUE ==
            socket_utility_ntoh32(EXPECTED_NETWORK_VALUE));

    /* doing the conversion twice undoes it. */
    TEST_EXPECT(
        EXPECTED_NETWORK_VALUE ==
            socket_utility_ntoh32(
                socket_utility_ntoh32(EXPECTED_NETWORK_VALUE)));
#endif
}
