/**
 * \file models/shadow/allocator/prop_allocator_valid.c
 *
 * \brief Check whether an allocator instance is valid.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>

#include "../../../src/allocator/allocator_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(allocator);

/**
 * \brief Valid allocator property.
 *
 * \param alloc         The allocator instance to be verified.
 *
 * \returns true if the allocator instance is valid.
 */
bool RCPR_SYM(property_allocator_valid)(const RCPR_SYM(allocator)* alloc)
{
    allocator_vtable* vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != alloc);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        alloc->RCPR_MODEL_STRUCT_TAG_REF(allocator), allocator);

    RCPR_MODEL_ASSERT(prop_resource_valid(&alloc->hdr));
    RCPR_MODEL_ASSERT(
        STATUS_SUCCESS
            == resource_vtable_read(&vtable, &alloc->hdr));

    /* verify that vtable is the correct size. */
    RCPR_MODEL_CHECK_OBJECT_READ(vtable, sizeof(*vtable));

    RCPR_MODEL_ASSERT(NULL != vtable->allocate_fn);
    RCPR_MODEL_ASSERT(NULL != vtable->reclaim_fn);

    return true;
}
