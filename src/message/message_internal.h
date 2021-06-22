/**
 * \file message/message_internal.h
 *
 * \brief Internal data types and functions for the fiber messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/message.h>
#include <rcpr/model_assert.h>
#include <rcpr/queue.h>
#include <rcpr/rbtree.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(message)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(message);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(mailbox_address) returnaddr;
    RCPR_SYM(mailbox_address) sendaddr;
    RCPR_SYM(resource)* payload;
};

typedef struct RCPR_SYM(mailbox) RCPR_SYM(mailbox);

struct RCPR_SYM(mailbox)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(mailbox);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(mailbox_address) address;
    RCPR_SYM(fiber)* blocked_fiber;
    RCPR_SYM(queue)* message_queue;
};

typedef struct RCPR_SYM(message_discipline_context)
RCPR_SYM(message_discipline_context);

struct RCPR_SYM(message_discipline_context)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(message_discipline_context);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(resource) discipline_cache;
    RCPR_SYM(fiber_scheduler)* sched;
    RCPR_SYM(rbtree)* mailboxes;
    uint64_t index;
};

/**
 * \brief Create a mailbox instance.
 *
 * \param mbox      Pointer to the pointer to which the mailbox is stored.
 * \param alloc     The allocator to use for this mailbox.
 * \param addr      The address of the new mailbox.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(mailbox_resource_create)(
    RCPR_SYM(mailbox)** mbox, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(mailbox_address) addr);

/**
 * \brief Create the message discipline context.
 *
 * \param ctx       Pointer to the pointer to which the context is stored.
 * \param alloc     The \ref allocator used to create the context;
 * \param sched     The \ref fiber_scheduler instance for this context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_context_create)(
    RCPR_SYM(resource)** ctx, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Override the resource release method for a message discipline.
 *
 * \param msgdisc       The message discipline to override.
 * \param context       The context to be released by this overridden release
 *                      method.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_set_resource_release)(
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc, RCPR_SYM(resource)* context);

/**
 * \brief The callback handler for a create mailbox request.
 *
 * \param context       Opaque pointer to the message discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_mailbox_create_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a close mailbox request.
 *
 * \param context       Opaque pointer to the message discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_mailbox_close_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a send message request.
 *
 * \param context       Opaque pointer to the message discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_message_send_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The callback handler for a receive message request.
 *
 * \param context       Opaque pointer to the message discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_message_receive_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/
#define RCPR_IMPORT_message_internal \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"") \
    typedef RCPR_SYM(mailbox) mailbox; \
    typedef RCPR_SYM(message_discipline_context) message_discipline_context; \
    static inline status mailbox_resource_create( \
        RCPR_SYM(mailbox)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(mailbox_address) z) { \
            return RCPR_SYM(mailbox_resource_create)(x,y,z); } \
    static inline status message_discipline_context_create( \
        RCPR_SYM(resource)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(fiber_scheduler)* z) { \
            return RCPR_SYM(message_discipline_context_create)(x,y,z); } \
    static inline status message_discipline_set_resource_release( \
        RCPR_SYM(fiber_scheduler_discipline)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(message_discipline_set_resource_release)(x,y); } \
    static inline status message_discipline_mailbox_create_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(message_discipline_mailbox_create_callback_handler)( \
                    w,x,y,z); } \
    static inline status message_discipline_mailbox_close_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(message_discipline_mailbox_close_callback_handler)( \
                    w,x,y,z); } \
    static inline status message_discipline_message_send_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(message_discipline_message_send_callback_handler)( \
                    w,x,y,z); } \
    static inline status message_discipline_message_receive_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
            return \
                RCPR_SYM(message_discipline_message_receive_callback_handler)( \
                    w,x,y,z); } \
    _Pragma("GCC diagnostic pop") \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
