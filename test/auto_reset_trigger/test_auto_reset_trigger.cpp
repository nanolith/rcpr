/**
 * \file test/auto_reset_trigger/test_auto_reset_trigger.cpp
 *
 * \brief Unit tests for auto_reset_trigger.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/auto_reset_trigger.h>

using namespace std;

RCPR_IMPORT_allocator;
RCPR_IMPORT_auto_reset_trigger;
RCPR_IMPORT_resource;

TEST_SUITE(auto_reset_trigger);

/**
 * Verify that we can create and release a \ref auto_reset_trigger instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    auto_reset_trigger* trigger = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an auto_reset_trigger. */
    TEST_ASSERT(
        STATUS_SUCCESS == auto_reset_trigger_create(&trigger, alloc));

    /* we should be able to release the trigger. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(auto_reset_trigger_resource_handle(trigger)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
