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

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct psock
{
    resource hdr;

    MODEL_STRUCT_TAG(psock);

    allocator* alloc;
    status (*read_fn)(psock* sock, void* data, size_t* size);
    status (*write_fn)(psock* sock, const void* data, size_t* size);
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
    fiber_scheduler* sched;
    fiber_scheduler_discipline* psock_discipline;
    psock_unexpected_handler_callback_fn unexpected;
};

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_read(psock* sock, void* data, size_t* size);

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
 * \brief Read data from the given async \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_wrap_async_read(psock* sock, void* data, size_t* size);

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
 * \brief Create a psock I/O discipline instance.
 *
 * \param disc          Pointer to a pointer that will hold the discipline
 *                      instance on success.
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
    fiber_scheduler_discipline** disc, fiber_scheduler* sched,
    allocator* alloc);

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
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

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
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

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
    resource** context, fiber_scheduler* sched, allocator* alloc);

/**
 * \brief Hook the fiber discipline resource release method in order to ensure
 * that the psock fiber discipline context resource is release as part of the
 * release of this fiber discipline resource.
 * 
 * \param disc          The discipline to override.
 * \param context       The discipline user context.
 */
void psock_fiber_scheduler_discipline_set_resource_release(
    fiber_scheduler_discipline* disc, resource* context);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
