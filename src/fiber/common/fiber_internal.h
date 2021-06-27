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

struct RCPR_SYM(fiber)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(fiber);

    void* stack_ptr;
    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(stack)* st;
    void* context;
    RCPR_SYM(fiber_fn) fn;
    RCPR_SYM(fiber_unexpected_event_callback_fn) unexpected_fn;
    const RCPR_SYM(rcpr_uuid)* restore_discipline_id;
    uint64_t restore_reason_code;
    void* restore_param;
};

struct RCPR_SYM(fiber_scheduler)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(fiber_scheduler);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(fiber)* current_fiber;
    RCPR_SYM(fiber)* main_fiber;
    void* context;
    RCPR_SYM(fiber_scheduler_callback_fn) fn;
    bool disciplined;
};

typedef struct RCPR_SYM(fiber_scheduler_disciplined_context)
RCPR_SYM(fiber_scheduler_disciplined_context);

struct RCPR_SYM(fiber_scheduler_disciplined_context)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(fiber_scheduler_disciplined_context);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(fiber_scheduler)* sched;
    RCPR_SYM(resource) cached_scheduler_resource_handler;
    RCPR_SYM(fiber)* main_fiber;
    RCPR_SYM(fiber)* idle_fiber;
    RCPR_SYM(fiber)* management_fiber;
    RCPR_SYM(rbtree)* fibers_by_pointer;
    RCPR_SYM(rbtree)* disciplines_by_uuid;
    RCPR_SYM(queue)* run_queue;
    RCPR_SYM(fiber_scheduler_discipline)* management_discipline;

    size_t callback_vector_size;
    RCPR_SYM(fiber_scheduler_discipline_callback_fn)* callback_vector;
    void** context_vector;
};

struct RCPR_SYM(fiber_scheduler_discipline)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(fiber_scheduler_discipline);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(rcpr_uuid) id;
    RCPR_SYM(fiber_scheduler)* sched;
    void* context;
    size_t callback_vector_size;
    RCPR_SYM(fiber_scheduler_discipline_callback_fn)* callback_vector;
    uint32_t* callback_codes;
};

extern const RCPR_SYM(rcpr_uuid) FIBER_SCHEDULER_INTERNAL_DISCIPLINE;

/**
 * \brief Release a fiber resource.
 *
 * \param r         The fiber resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(fiber_resource_release)(RCPR_SYM(resource)* r);

/**
 * \brief Entry point for a fiber.
 *
 * \param sched     The fiber scheduler.
 * \param fib       The fiber being entered.
 *
 * \note Does not return.
 */
status
RCPR_SYM(fiber_entry)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib);

/**
 * \brief Pointer type for the fiber entry function.
 */
typedef
status (*RCPR_SYM(fiber_entry_fn))(
    RCPR_SYM(fiber_scheduler)*, RCPR_SYM(fiber)*);

/**
 * \brief Assembler routine to switch between two fibers.
 *
 * \param prev      The previous (current) fiber.
 * \param next      The next (switching) fiber.
 * \param disc      The restore discipline id.
 * \param event     The resume event to give to the next fiber.
 * \param param     The resume parameter to give to the next fiber.
 */
void RCPR_SYM(fiber_switch)(
    RCPR_SYM(fiber)* prev, RCPR_SYM(fiber)* next,
    const RCPR_SYM(rcpr_uuid)* disc, int64_t event, void *param);

/**
 * \brief Assembler routine to set up a fiber for entry.
 *
 * \param fib       The fiber instance to set up.
 * \param sched     The scheduler on which this fiber runs.
 * \param entry     The fiber entry point.
 */
void RCPR_SYM(fiber_make)(
    RCPR_SYM(fiber)* fib, RCPR_SYM(fiber_scheduler)* sched,
    RCPR_SYM(fiber_entry_fn) entry);

/**
 * \brief Release a fiber scheduler resource.
 *
 * \param r         The fiber scheduler resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(fiber_scheduler_resource_release)(RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/
#define RCPR_IMPORT_fiber_internal \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"") \
    typedef RCPR_SYM(fiber_scheduler_disciplined_context) \
    fiber_scheduler_disciplined_context; \
    typedef RCPR_SYM(fiber_entry_fn) fiber_entry_fn; \
    static inline status fiber_resource_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(fiber_resource_release)(x); } \
    static inline status fiber_entry( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return RCPR_SYM(fiber_entry)(x, y); } \
    static inline void fiber_switch( \
        RCPR_SYM(fiber)* v, RCPR_SYM(fiber)* w, const RCPR_SYM(rcpr_uuid)* x, \
        int64_t y, void* z) { \
            RCPR_SYM(fiber_switch)(v,w,x,y,z); } \
    static inline void fiber_make( \
        RCPR_SYM(fiber)* x, RCPR_SYM(fiber_scheduler)* y, \
        RCPR_SYM(fiber_entry_fn) z) { \
            RCPR_SYM(fiber_make)(x,y,z); } \
    static inline status fiber_scheduler_resource_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(fiber_scheduler_resource_release)(x); } \
    _Pragma("GCC diagnostic pop") \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
