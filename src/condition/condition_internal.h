/**
 * \file condition/condition_internal.h
 *
 * \brief Internal data types and functions for the fiber messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/condition.h>
#include <rcpr/model_assert.h>
#include <rcpr/queue.h>
#include <rcpr/rbtree.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

typedef struct RCPR_SYM(condition_barrier) RCPR_SYM(condition_barrier);

struct RCPR_SYM(condition_barrier)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(condition_barrier);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(conditional) cond;
    RCPR_SYM(slist)* wait_list;
};

typedef struct RCPR_SYM(condition_discipline_context)
RCPR_SYM(condition_discipline_context);

struct RCPR_SYM(condition_discipline_context)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(condition_discipline_context);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(resource) discipline_cache;
    RCPR_SYM(fiber_scheduler)* sched;
    RCPR_SYM(rbtree)* condition_barriers;
    uint64_t index;
};

/**
 * \brief Create a \ref condition_barrier instance.
 *
 * \param cstruct   Pointer to the pointer to which the condition barrier is
 *                  stored.
 * \param alloc     The allocator to use for this condition barrier.
 * \param cond      The handle for the conditional.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_barrier_create)(
    RCPR_SYM(condition_barrier)** cstruct, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(conditional) cond);

/**
 * \brief Create the condition discipline context.
 *
 * \param ctx       Pointer to the pointer to which the context is stored.
 * \param alloc     The \ref allocator used to create the context;
 * \param sched     The \ref fiber_scheduler instance for this context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_context_create)(
    RCPR_SYM(resource)** ctx, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Override the resource release method for a condition discipline.
 *
 * \param condisc       The message discipline to override.
 * \param context       The context to be released by this overridden release
 *                      method.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_set_resource_release)(
    RCPR_SYM(fiber_scheduler_discipline)* condisc, RCPR_SYM(resource)* context);

/**
 * \brief The callback handler for a create conditional request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_create_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a close conditional request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_close_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a conditional wait request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_wait_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a conditional notify one request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_notify_one_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a conditional notify all request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_notify_all_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/
#define RCPR_IMPORT_condition_internal \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(condition_barrier) condition_barrier; \
    typedef RCPR_SYM(condition_discipline_context) \
    condition_discipline_context; \
    static inline status condition_barrier_create( \
        RCPR_SYM(condition_barrier)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(conditional) z) { \
            return RCPR_SYM(condition_barrier_create)(x,y,z); } \
    static inline status condition_discipline_context_create( \
        RCPR_SYM(resource)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(fiber_scheduler)* z) { \
            return RCPR_SYM(condition_discipline_context_create)(x,y,z); } \
    static inline status condition_discipline_set_resource_release( \
        RCPR_SYM(fiber_scheduler_discipline)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(condition_discipline_set_resource_release)(x,y); } \
    static inline status condition_discipline_create_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(condition_discipline_create_callback_handler)( \
                    w,x,y,z); } \
    static inline status condition_discipline_close_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(condition_discipline_close_callback_handler)( \
                    w,x,y,z); } \
    static inline status condition_discipline_wait_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(condition_discipline_wait_callback_handler)( \
                    w,x,y,z); } \
    static inline status condition_discipline_notify_one_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(condition_discipline_notify_one_callback_handler)( \
                    w,x,y,z); } \
    static inline status condition_discipline_notify_all_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(condition_discipline_notify_all_callback_handler)( \
                    w,x,y,z); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
