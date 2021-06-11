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

struct message
{
    resource hdr;

    MODEL_STRUCT_TAG(message);

    allocator* alloc;
    mailbox_address returnaddr;
    mailbox_address sendaddr;
    resource* payload;
};

typedef struct mailbox mailbox;

struct mailbox
{
    resource hdr;

    MODEL_STRUCT_TAG(mailbox);

    allocator* alloc;
    mailbox_address address;
    fiber* blocked_fiber;
    queue* message_queue;
};

typedef struct message_discipline_context message_discipline_context;

struct message_discipline_context
{
    resource hdr;

    MODEL_STRUCT_TAG(message_discipline_context);

    allocator* alloc;
    resource discipline_cache;
    fiber_scheduler* sched;
    rbtree* mailboxes;
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
status mailbox_resource_create(
    mailbox** mbox, allocator* alloc, mailbox_address addr);

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
status message_discipline_context_create(
    resource** ctx, allocator* alloc, fiber_scheduler* sched);

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
status message_discipline_set_resource_release(
    fiber_scheduler_discipline* msgdisc, resource* context);

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
status message_discipline_mailbox_create_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

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
status message_discipline_mailbox_close_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

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
status message_discipline_message_send_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

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
status message_discipline_message_receive_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
