/**
 * \file test/fiber/test_fiber_scheduler_discipline_add.cpp
 *
 * \brief Unit tests for fiber_scheduler_discipline_add.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <string.h>

#include "../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(fiber_scheduler_discipline_add);

static status dummy_scheduler_callback(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, const rcpr_uuid** restore_disc_id, int* resume_event,
    void** resume_param)
{
    /* is this a main fiber add? */
    if (FIBER_SCHEDULER_YIELD_EVENT_MAIN == yield_event)
    {
        *resume_fib = yield_fib;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_MAIN;
        *resume_param = nullptr;

        return STATUS_SUCCESS;
    }
    else if (FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE == yield_event)
    {
        *resume_fib = NULL;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_RESOURCE_RELEASE;
        *resume_param = nullptr;

        return STATUS_SUCCESS;
    }
    else
    {
        return -1;
    }
}

/**
 * Verify that we can add a fiber scheduler discipline instance.
 */
TEST(add)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;
    rcpr_uuid id = { .data = {
        0x0e, 0x2c, 0xfc, 0x92, 0x89, 0xfa, 0x46, 0x54,
        0xb9, 0x69, 0xd7, 0x1b, 0x18, 0x46, 0x9b, 0x4c } };
    fiber_scheduler_discipline_callback_fn emptyvec[0];

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create a fiber scheduler discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_discipline_create(
                &disc, &id, alloc, NULL, 0, emptyvec));

    /* we should be able to add the discipline to our fiber scheduler. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_discipline_add(sched, disc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that adding a discipline to an undisciplined scheduler fails.
 */
TEST(add_undisciplined)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;
    rcpr_uuid id = { .data = {
        0x0e, 0x2c, 0xfc, 0x92, 0x89, 0xfa, 0x46, 0x54,
        0xb9, 0x69, 0xd7, 0x1b, 0x18, 0x46, 0x9b, 0x4c } };
    fiber_scheduler_discipline_callback_fn emptyvec[0];

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create an undisciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create(
                &sched, alloc, nullptr, &dummy_scheduler_callback));

    /* we should be able to create a fiber scheduler discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_discipline_create(
                &disc, &id, alloc, NULL, 0, emptyvec));

    /* adding to an undisciplined fiber scheduler should fail. */
    TEST_ASSERT(
        ERROR_FIBER_SCHEDULER_NOT_DISCIPLINED ==
            fiber_scheduler_discipline_add(sched, disc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_discipline_resource_handle(disc)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that adding the same discipline ID twice fails.
 */
TEST(double_add)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;
    rcpr_uuid id = { .data = {
        0x0e, 0x2c, 0xfc, 0x92, 0x89, 0xfa, 0x46, 0x54,
        0xb9, 0x69, 0xd7, 0x1b, 0x18, 0x46, 0x9b, 0x4c } };
    fiber_scheduler_discipline_callback_fn emptyvec[0];

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create a fiber scheduler discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_discipline_create(
                &disc, &id, alloc, NULL, 0, emptyvec));

    /* we should be able to add the discipline to our fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_discipline_add(sched, disc));

    /* force the discipline to NOT be owned before calling. */
    disc->sched = nullptr;

    /* Attempting to add the discipline a second time should fail. */
    TEST_ASSERT(
        ERROR_FIBER_SCHEDULER_DUPLICATE_DISCIPLINE_ID ==
            fiber_scheduler_discipline_add(sched, disc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that adding a discipline fails if the fiber scheduler pointer is
 * already set.
 */
TEST(already_owned)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;
    rcpr_uuid id = { .data = {
        0x0e, 0x2c, 0xfc, 0x92, 0x89, 0xfa, 0x46, 0x54,
        0xb9, 0x69, 0xd7, 0x1b, 0x18, 0x46, 0x9b, 0x4c } };
    fiber_scheduler_discipline_callback_fn emptyvec[0];

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create a fiber scheduler discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_discipline_create(
                &disc, &id, alloc, NULL, 0, emptyvec));

    /* force the discipline to be owned before calling. */
    disc->sched = sched;

    /* Adding the discipline should fail because the discipline is already
     * owned. */
    TEST_ASSERT(
        ERROR_FIBER_SCHEDULER_DISCIPLINE_ALREADY_OWNED ==
            fiber_scheduler_discipline_add(sched, disc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_discipline_resource_handle(disc)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
