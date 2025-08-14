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

static void test_callback(int* context)
{
    *context += 1;
}

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

/**
 * Verify that with a registered callback, we can signal the trigger.
 */
TEST(signal_with_callback)
{
    allocator* alloc = nullptr;
    auto_reset_trigger* trigger = nullptr;
    int call_count = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an auto_reset_trigger. */
    TEST_ASSERT(
        STATUS_SUCCESS == auto_reset_trigger_create(&trigger, alloc));

    /* we can register a callback. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == auto_reset_trigger_register(
                    trigger, (auto_reset_trigger_callback)&test_callback,
                    &call_count));

    /* signal the trigger. */
    auto_reset_trigger_signal(trigger);

    /* precondition: called is false. */
    TEST_ASSERT(0 == call_count);

    /* step the trigger. */
    auto_reset_trigger_step(trigger);

    /* postcondition: our listener was called once. */
    TEST_ASSERT(1 == call_count);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(auto_reset_trigger_resource_handle(trigger)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that without a registered callback, multiple signals and steps do
 * nothing, but once we register and step, the callback is called once.
 */
TEST(multiple_signal_step_then_register_step)
{
    allocator* alloc = nullptr;
    auto_reset_trigger* trigger = nullptr;
    int call_count = 0;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an auto_reset_trigger. */
    TEST_ASSERT(
        STATUS_SUCCESS == auto_reset_trigger_create(&trigger, alloc));

    /* signal and step the trigger; nothing happens. */
    for (int i = 0; i < 10; ++i)
    {
        auto_reset_trigger_signal(trigger);
        auto_reset_trigger_step(trigger);
    }

    /* register a callback. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == auto_reset_trigger_register(
                    trigger, (auto_reset_trigger_callback)&test_callback,
                    &call_count));

    /* precondition: called is false. */
    TEST_ASSERT(0 == call_count);

    /* step the trigger. */
    auto_reset_trigger_step(trigger);

    /* postcondition: our listener was called once. */
    TEST_ASSERT(1 == call_count);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(auto_reset_trigger_resource_handle(trigger)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
