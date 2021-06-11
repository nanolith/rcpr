/**
 * \file test/message/test_message_discipline_get_or_create.cpp
 *
 * \brief Unit tests for message_discipline_get_or_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/message.h>

TEST_SUITE(message_discipline_get_or_create);

/**
 * Verify that we can create and a message discipline instance.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the message discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_discipline_get_or_create(&disc, alloc, sched));

    /* the discipline should not be NULL. */
    TEST_EXPECT(nullptr != disc);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that the second call to get_or_create returns the same discipline.
 */
TEST(get)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;
    fiber_scheduler_discipline* disc2 = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the message discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_discipline_get_or_create(&disc, alloc, sched));

    /* the discipline should not be NULL. */
    TEST_EXPECT(nullptr != disc);

    /* we can call get_or_create a second time. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            message_discipline_get_or_create(&disc2, alloc, sched));

    /* the discipline should not be NULL. */
    TEST_EXPECT(nullptr != disc2);

    /* the two disciplines are the same. */
    TEST_EXPECT(disc == disc2);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}
