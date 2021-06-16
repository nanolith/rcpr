/**
 * \file test/uuid/test_rcpr_uuid_to_string.cpp
 *
 * \brief Unit tests for rcpr_uuid_to_string.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/uuid.h>
#include <string.h>

#include <iostream>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

TEST_SUITE(rcpr_uuid_to_string);

/**
 * Test that the all-zero uuid can be converted to a string.
 */
TEST(zero_uuid)
{
    const rcpr_uuid ZERO_UUID = {
        .data = { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } };
    const char* EXPECTED_STRING = "00000000-0000-0000-0000-000000000000";
    char* value = nullptr;
    allocator* alloc = nullptr;

    /* create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* converting to a string should succeed. */
    TEST_ASSERT(
        STATUS_SUCCESS == rcpr_uuid_to_string(&value, alloc, &ZERO_UUID));

    /* it should match our string. */
    TEST_EXPECT(0 == strcmp(value, EXPECTED_STRING));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == allocator_reclaim(alloc, value));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Test that an arbitrary uuid is converted correctly.
 */
TEST(arbitrary_uuid)
{
    const rcpr_uuid ARBITRARY_UUID = {
        .data = { 0x68, 0x60, 0x0d, 0xca, 0x07, 0x58, 0x4e, 0xa5,
                  0x8e, 0x6c, 0x1c, 0x14, 0xf3, 0x67, 0x03, 0xae } };
    const char* EXPECTED_STRING = "68600dca-0758-4ea5-8e6c-1c14f36703ae";
    char* value = nullptr;
    allocator* alloc = nullptr;

    /* create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* converting to a string should succeed. */
    TEST_ASSERT(
        STATUS_SUCCESS == rcpr_uuid_to_string(&value, alloc, &ARBITRARY_UUID));

    /* it should match our string. */
    TEST_EXPECT(0 == strcmp(value, EXPECTED_STRING));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == allocator_reclaim(alloc, value));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
