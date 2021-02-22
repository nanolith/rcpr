/**
 * \file fiber/common/fiber_internal.h
 *
 * \brief Internal data types and functions for fiber.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>
#include <rcpr/stack.h>

#include "../../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct fiber
{
    resource hdr;

    MODEL_STRUCT_TAG(fiber);

    allocator* alloc;
    stack* st;
    void* context;
    fiber_fn fn;
};

struct fiber_scheduler
{
    resource hdr;

    MODEL_STRUCT_TAG(fiber_scheduler);

    allocator* alloc;
    fiber* main_fiber;
    void* context;
    fiber_scheduler_callback_fn fn;
};

/**
 * \brief Release a fiber resource.
 *
 * \param r         The fiber resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status fiber_resource_release(resource* r);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
