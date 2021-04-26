/**
 * \file test/fiber/test_fiber_unexpected_event_callback_add.cpp
 *
 * \brief Unit tests for fiber_unexpected_event_callback_add.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>

#include "../../src/fiber/common/fiber_internal.h"

TEST_SUITE(fiber_unexpected_event_callback_add);

static status dummy_event(
    void* context, const rcpr_uuid* resume_disc_id, int resume_event,
    void* resume_param)
{
    return STATUS_SUCCESS;
}

/**
 * Verify that we can add an unexpected event callback function to a fiber.
 */
TEST(add)
{
    allocator* alloc = nullptr;
    fiber* f = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a fiber for a thread. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_create_for_thread(&f, alloc));

    /* PRECONDITION: fiber unexpected event callback not set. */
    TEST_ASSERT(nullptr == f->unexpected_fn);

    /* add a custom event callback to this fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS == fiber_unexpected_event_callback_add(f, &dummy_event));

    /* POSTCONDITION: fiber unexpected event callback is set. */
    TEST_EXPECT(&dummy_event == f->unexpected_fn);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_resource_handle(f)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}