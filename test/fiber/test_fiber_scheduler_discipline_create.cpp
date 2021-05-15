/**
 * \file test/fiber/test_fiber_scheduler_discipline_create.cpp
 *
 * \brief Unit tests for fiber_scheduler_discipline_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

TEST_SUITE(fiber_scheduler_discipline_create);

/**
 * Verify that we can create a fiber scheduler discipline instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler_discipline* disc = nullptr;
    rcpr_uuid id = { .data = {
        0x0e, 0x2c, 0xfc, 0x92, 0x89, 0xfa, 0x46, 0x54,
        0xb9, 0x69, 0xd7, 0x1b, 0x18, 0x46, 0x9b, 0x4c } };
    fiber_scheduler_discipline_callback_fn emptyvec[0];

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a fiber scheduler discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_discipline_create(
                &disc, &id, alloc, NULL, 0, emptyvec));

    /* we should be able to release the fiber scheduler discipline instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_discipline_resource_handle(disc)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
