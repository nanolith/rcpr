/**
 * \file test/psock/async/test_psock_fiber_scheduler_discipline_create.cpp
 *
 * \brief Unit tests for psock_fiber_scheduler_discipline_create.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <sys/socket.h>
#include <unistd.h>

#include "../../../src/psock/psock_internal.h"

TEST_SUITE(psock_fiber_scheduler_discipline_create);

#if 0
/**
 * Verify that we can create a fiber scheduler discipline for psock I/O.
 */
TEST(create)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber_scheduler_discipline* disc = nullptr;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a fiber scheduler with disciplines. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* we should be able to create the psock fiber scheduler discipline. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_fiber_scheduler_discipline_create(&disc, sched, alloc));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
#endif
