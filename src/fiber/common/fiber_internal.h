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
#include <rcpr/queue.h>
#include <rcpr/rbtree.h>
#include <rcpr/stack.h>
#include <rcpr/uuid.h>

#include "../../stack/stack_internal.h"
#include "../../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct fiber
{
    resource hdr;

    MODEL_STRUCT_TAG(fiber);

    void* stack_ptr;
    allocator* alloc;
    stack* st;
    void* context;
    fiber_fn fn;
    fiber_unexpected_event_callback_fn unexpected_fn;
    const rcpr_uuid* restore_discipline_id;
    uint64_t restore_reason_code;
    void* restore_param;
};

struct fiber_scheduler
{
    resource hdr;

    MODEL_STRUCT_TAG(fiber_scheduler);

    allocator* alloc;
    fiber* current_fiber;
    fiber* main_fiber;
    void* context;
    fiber_scheduler_callback_fn fn;
    bool disciplined;
};

typedef struct fiber_scheduler_disciplined_context
fiber_scheduler_disciplined_context;

struct fiber_scheduler_disciplined_context
{
    resource hdr;

    MODEL_STRUCT_TAG(fiber_scheduler_disciplined_context);

    allocator* alloc;
    fiber_scheduler* sched;
    resource cached_scheduler_resource_handler;
    fiber* main_fiber;
    fiber* idle_fiber;
    rbtree* fibers_by_pointer;
    rbtree* disciplines_by_uuid;
    queue* run_queue;

    size_t callback_vector_size;
    fiber_scheduler_discipline_callback_fn* callback_vector;
    void** context_vector;
};

struct fiber_scheduler_discipline
{
    resource hdr;

    MODEL_STRUCT_TAG(fiber_scheduler_discipline);

    allocator* alloc;
    rcpr_uuid id;
    fiber_scheduler* sched;
    void* context;
    size_t callback_vector_size;
    fiber_scheduler_discipline_callback_fn* callback_vector;
    uint32_t* callback_codes;
};

extern const rcpr_uuid FIBER_SCHEDULER_INTERNAL_DISCIPLINE;

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

/**
 * \brief Entry point for a fiber.
 *
 * \param sched     The fiber scheduler.
 * \param fib       The fiber being entered.
 *
 * \note Does not return.
 */
status fiber_entry(fiber_scheduler* sched, fiber* fib);

/**
 * \brief Pointer type for the fiber entry function.
 */
typedef
status (*fiber_entry_fn)(fiber_scheduler*, fiber*);

/**
 * \brief Assembler routine to switch between two fibers.
 *
 * \param prev      The previous (current) fiber.
 * \param next      The next (switching) fiber.
 * \param disc      The restore discipline id.
 * \param event     The resume event to give to the next fiber.
 * \param param     The resume parameter to give to the next fiber.
 */
void fiber_switch(
    fiber* prev, fiber* next, const rcpr_uuid* disc, int64_t event,
    void *param);

/**
 * \brief Assembler routine to set up a fiber for entry.
 *
 * \param fib       The fiber instance to set up.
 * \param sched     The scheduler on which this fiber runs.
 * \param entry     The fiber entry point.
 */
void fiber_make(fiber* fib, fiber_scheduler* sched, fiber_entry_fn entry);

/**
 * \brief Release a fiber scheduler resource.
 *
 * \param r         The fiber scheduler resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status fiber_scheduler_resource_release(resource* r);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
