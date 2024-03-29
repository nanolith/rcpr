/**
 * \file test/resource/test_resource_release_vtable.cpp
 *
 * \brief Unit tests for resource_release and vtable checks.
 */

#include <minunit/minunit.h>
#include <rcpr/resource.h>
#include <rcpr/resource/protected.h>
#include <rcpr/vtable.h>

TEST_SUITE(resource_release_vtable);

RCPR_IMPORT_resource;

#ifdef RCPR_VTABLE_RUNTIME_ENFORCEMENT

static status good_resource_function(resource* r);

RCPR_VTABLE
resource_vtable good_resource_vtable = {
    &good_resource_function };

resource_vtable hackable_vtable = {
    &good_resource_function };

/**
 * Verify that a vtable pointing to a custom function is executed.
 */
TEST(basics)
{
    resource r;

    resource_init(&r, &good_resource_vtable);

    TEST_EXPECT(STATUS_SUCCESS == resource_release(&r));
}

#ifndef RCPR_VTABLE_CHECK_ASSERT

static status bad_resource_function(resource* r);

/**
 * Verify that if we attempt to "hack" a vtable at runtime, the vtable check
 * will fail.
 */
TEST(hack_failure)
{
    resource r;

    hackable_vtable.release = &bad_resource_function;

    resource_init(&r, &hackable_vtable);

    TEST_EXPECT(ERROR_GENERAL_BAD_VTABLE == resource_release(&r));
}

static status bad_resource_function(resource* r)
{
    (void)r;

    return -1;
}

#endif /*RCPR_VTABLE_CHECK_ASSERT*/

static status good_resource_function(resource* r)
{
    (void)r;

    return STATUS_SUCCESS;
}

#endif /*RCPR_VTABLE_RUNTIME_ENFORCEMENT*/
