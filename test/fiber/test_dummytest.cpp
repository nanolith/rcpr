/**
 * \file test/test_dummytest.cpp
 *
 * \brief Stub unit tests for stub "dummytest" assembler function.
 */

#include <minunit/minunit.h>

TEST_SUITE(fiber_dummytest);

/* forward decls */
extern "C" int dummytest(int x, int y, int z);

/**
 * Verify compilation and linkage of sysv assembler.
 */
TEST(basics)
{
    TEST_ASSERT(
        3 == dummytest(1, 2, 3));
    TEST_ASSERT(
        3 == dummytest(3, 2, 1));
    TEST_ASSERT(
        3 == dummytest(1, 3, 2));
}
