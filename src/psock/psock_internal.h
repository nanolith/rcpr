/**
 * \file psock/psock_internal.h
 *
 * \brief Internal data types and functions for psock.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>
#include <sys/socket.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

enum psock_type
{
    PSOCK_TYPE_DESCRIPTOR               = 0x0001,
    PSOCK_TYPE_WRAP_ASYNC               = 0x0002,
};

struct psock
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(psock);
    int type;

    RCPR_SYM(allocator)* alloc;
    status (*read_fn)(psock* sock, void* data, size_t* size, bool block);
    status (*write_fn)(psock* sock, const void* data, size_t* size);
    status (*accept_fn)(
        psock* sock, int* desc, struct sockaddr* addr, socklen_t* addrlen);
};

/* forward decls for psock_from_descriptor. */
struct psock_from_descriptor;
typedef struct psock_from_descriptor psock_from_descriptor;

struct psock_from_descriptor
{
    psock hdr;
    int descriptor;
};

/* forward decls for psock_wrap_async. */
struct psock_wrap_async;
typedef struct psock_wrap_async psock_wrap_async;

struct psock_wrap_async
{
    psock hdr;
    psock* wrapped;
    RCPR_SYM(fiber_scheduler)* sched;
    RCPR_SYM(fiber_scheduler_discipline)* psock_discipline;
    psock_unexpected_handler_callback_fn unexpected;
    void* context;
    int flags;
};

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Ignored for raw descriptor reads.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_read(
    psock* sock, void* data, size_t* size, bool block);

/**
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_write(psock* sock, const void* data, size_t* size);

/**
 * \brief Accept a socket from a \ref psock listen socket instance.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param desc          Pointer to the integer field to hold the accepted
 *                      descriptor.
 * \param addr          The address of the accepted socket.
 * \param addrlen       On input, the max size of the address field; on output,
 *                      the size of the address field.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_accept(
    psock* sock, int* desc, struct sockaddr* addr, socklen_t* addrlen);

/**
 * \brief Release a psock_from_descriptor resource.
 *
 * \param r             Pointer to the psock_from_descriptor resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status psock_from_descriptor_release(RCPR_SYM(resource)* r);

/**
 * \brief Read data from the given async \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Set to true if the read should block until all bytes are
 *                      read.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_wrap_async_read(psock* sock, void* data, size_t* size, bool block);

/**
 * \brief Write data to the given async \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_wrap_async_write(psock* sock, const void* data, size_t* size);

/**
 * \brief Accept a socket from a \ref psock listen socket instance.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param idesc         Pointer to the integer field to hold the accepted
 *                      descriptor.
 * \param addr          The address of the accepted socket.
 * \param addrlen       On input, the max size of the address field; on output,
 *                      the size of the address field.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_wrap_async_accept(
    psock* sock, int* idesc, struct sockaddr* addr, socklen_t* addrlen);

/**
 * \brief Create a psock I/O discipline instance.
 *
 * \param disc          Pointer to a pointer that will hold the discipline
 *                      instance on success.
 * \param context       Pointer to a pointer to receive the context to send to
 *                      the idle fiber.
 * \param sched         The scheduler to be used for this discipline.
 * \param alloc         The allocator to use to create this instance.
 *
 * \note This only creates the discipline, it does not add it to the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_fiber_scheduler_discipline_create(
    RCPR_SYM(fiber_scheduler_discipline)** disc, RCPR_SYM(resource)** context,
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(allocator)* alloc);

/**
 * \brief Callback for read wait events.
 *
 * \param context       The user context for this callback.
 * \param yield_fib     The yielding fiber for this event.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   The yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
status psock_fiber_scheduler_disciplined_read_wait_callback_handler(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief Callback for write wait events.
 *
 * \param context       The user context for this callback.
 * \param yield_fib     The yielding fiber for this event.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   The yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
status psock_fiber_scheduler_disciplined_write_wait_callback_handler(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief The entry point for the psock idle fiber.
 *
 * This idle fiber handles the platform-specific event loop for I/O events, and
 * will sleep until a descriptor is available for a requested read or write.
 *
 * \param context       The user context for this fiber.
 *
 * \returns a status code indicating success or failure when this fiber
 * terminates.
 */
status psock_idle_fiber_entry(void* context);

/**
 * \brief Create a platform-specific fiber scheduler discipline context for
 * psock I/O.
 *
 * \param context       Pointer to receive the context pointer on success.
 * \param sched         The fiber scheduler to which this discipline will
 *                      belong.
 * \param alloc         The allocator to use to create this resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status psock_fiber_scheduler_discipline_context_create(
    RCPR_SYM(resource)** context, RCPR_SYM(fiber_scheduler)* sched,
    RCPR_SYM(allocator)* alloc);

/**
 * \brief Hook the fiber discipline resource release method in order to ensure
 * that the psock fiber discipline context resource is release as part of the
 * release of this fiber discipline resource.
 * 
 * \param disc          The discipline to override.
 * \param context       The discipline user context.
 */
void psock_fiber_scheduler_discipline_set_resource_release(
    RCPR_SYM(fiber_scheduler_discipline)* disc, RCPR_SYM(resource)* context);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
