/**
 * \file test/control/test_control.cpp
 *
 * \brief Unit tests for control macros.
 */

#include <minunit/minunit.h>
#include <rcpr/control.h>

TEST_SUITE(control_macros);

/**
 * Verify that we if an operation succeeds, control falls through.
 */
TEST(try_success)
{
    CONTROL_PREAMBLE;

    /* this should not jump to assertion_fail. */
    TRY_OR_FAIL(STATUS_SUCCESS, assertion_fail);
    goto done;

assertion_fail:
    TEST_FAILURE();
    return;

done:
    TEST_SUCCESS();
    return;
}

/**
 * Verify that we if an operation fails, control jumps to the failure point.
 */
TEST(try_failure)
{
    CONTROL_PREAMBLE;

    /* this should not jump to assertion_fail. */
    TRY_OR_FAIL(-1, assertion_fail);
    goto done;

assertion_fail:
    TEST_SUCCESS();
    return;

done:
    TEST_FAILURE();
    return;
}

/**
 * Verify that if a cleanup operation succeeds, the return code is NOT updated.
 */
TEST(cleanup_success)
{
    CONTROL_PREAMBLE;
    const status EXPECTED_ERROR_CODE = 5;
    const status CASCADE_RESULT = STATUS_SUCCESS;

    /* set the expected error code. */
    retval = EXPECTED_ERROR_CODE;

    /* run the cleanup operation, cascading errors. */
    CLEANUP_OR_CASCADE(CASCADE_RESULT);

    /* when the cleanup operation succeeds, the return value is unchanged. */
    TEST_EXPECT(EXPECTED_ERROR_CODE == retval);
}

/**
 * Verify that if a cleanup operation fails, the return code is updated.
 */
TEST(cleanup_failure)
{
    CONTROL_PREAMBLE;
    const status EXPECTED_ERROR_CODE = 5;
    const status CASCADE_RESULT = 6;

    /* set the expected error code. */
    retval = EXPECTED_ERROR_CODE;

    /* run the cleanup operation, cascading errors. */
    CLEANUP_OR_CASCADE(CASCADE_RESULT);

    /* when the cleanup operation fails, the return value is changed. */
    TEST_EXPECT(CASCADE_RESULT == retval);
}
