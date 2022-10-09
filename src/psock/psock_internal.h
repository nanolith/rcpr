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
#include <rcpr/slist.h>
#include <sys/socket.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

enum psock_type
{
    PSOCK_TYPE_DESCRIPTOR               = 0x0001,
    PSOCK_TYPE_BUFFER                   = 0x0002,
    PSOCK_TYPE_WRAP_ASYNC               = 0x0003,
    PSOCK_TYPE_BUFFERED                 = 0x0004,
    PSOCK_TYPE_USER                     = 0x0005,
};

struct RCPR_SYM(psock)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(psock);
    int type;
    int socktype;

    RCPR_SYM(allocator)* alloc;
    status (*read_fn)(
        RCPR_SYM(psock)* sock, void* data, size_t* size, bool block);
    status (*write_fn)(
        RCPR_SYM(psock)* sock, const void* data, size_t* size);
    status (*accept_fn)(
        RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
        socklen_t* addrlen);
    status (*sendmsg_fn)(
        RCPR_SYM(psock)* sock, const struct msghdr* msg, int flags);
    status (*recvmsg_fn)(
        RCPR_SYM(psock)* sock, struct msghdr* msg, size_t* len, int flags);
};

/* set a reasonable buffer size. */
#define PSOCK_BR_BUFFER_SIZE 16384

struct RCPR_SYM(psock_br)
{
    RCPR_SYM(psock) hdr;
    RCPR_SYM(psock)* wrapped;

    RCPR_MODEL_STRUCT_TAG(psock_br);

    uint8_t* buffer;
    size_t max_size;
    size_t current_size;
    size_t offset;
};

/* forward decls for psock_from_descriptor. */
typedef struct RCPR_SYM(psock_from_descriptor) RCPR_SYM(psock_from_descriptor);

struct RCPR_SYM(psock_from_descriptor)
{
    RCPR_SYM(psock) hdr;
    int descriptor;
};

/* forward decls for psock_wrap_async. */
typedef struct RCPR_SYM(psock_wrap_async) RCPR_SYM(psock_wrap_async);

struct RCPR_SYM(psock_wrap_async)
{
    RCPR_SYM(psock) hdr;
    RCPR_SYM(psock)* wrapped;
    RCPR_SYM(fiber)* fib;
    RCPR_SYM(fiber_scheduler_discipline)* psock_discipline;
    int flags;
};

#define PSOCK_BUFFER_SIZE 4096

/* forward decls for psock_from_buffer. */
typedef struct RCPR_SYM(psock_from_buffer) RCPR_SYM(psock_from_buffer);

struct RCPR_SYM(psock_from_buffer)
{
    RCPR_SYM(psock) hdr;
    char* input_buffer;
    size_t input_buffer_size;
    char* output_curr_buffer;
    RCPR_SYM(slist)* output_queue;
    size_t output_buffer_size;
    size_t output_buffer_total_size;
    size_t buffer_read_offset;
    size_t buffer_write_offset;
};

/* forward decl for output buffer node. */
typedef struct RCPR_SYM(psock_output_buffer_node)
RCPR_SYM(psock_output_buffer_node);

struct RCPR_SYM(psock_output_buffer_node)
{
    RCPR_SYM(resource) hdr;
    RCPR_SYM(allocator)* alloc;
    char* buffer;
    size_t size;
};

/* forward decls for psock_ex. */
typedef struct RCPR_SYM(psock_ex) RCPR_SYM(psock_ex);

struct RCPR_SYM(psock_ex)
{
    RCPR_SYM(psock) hdr;
    void* ctx;
    RCPR_SYM(psock_read_fn) ex_read_fn;
    RCPR_SYM(psock_write_fn) ex_write_fn;
    RCPR_SYM(psock_accept_fn) ex_accept_fn;
    RCPR_SYM(psock_release_fn) ex_release_fn;
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
status RCPR_SYM(psock_from_descriptor_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block);

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
status RCPR_SYM(psock_from_descriptor_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size);

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
status RCPR_SYM(psock_from_descriptor_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_sendmsg)(
    RCPR_SYM(psock)* sock, const struct msghdr* msg, int flags);

/**
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_recvmsg)(
    RCPR_SYM(psock)* sock, struct msghdr* msg, size_t* len, int flags);

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
status RCPR_SYM(psock_from_descriptor_release)(RCPR_SYM(resource)* r);

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
status RCPR_SYM(psock_wrap_async_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block);

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
status RCPR_SYM(psock_wrap_async_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size);

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
status RCPR_SYM(psock_wrap_async_accept)(
    RCPR_SYM(psock)* sock, int* idesc, struct sockaddr* addr,
    socklen_t* addrlen);

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_sendmsg)(
    RCPR_SYM(psock)* sock, const struct msghdr* msg, int flags);

/**
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_recvmsg)(
    RCPR_SYM(psock)* sock, struct msghdr* msg, size_t* len, int flags);

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
status RCPR_SYM(psock_fiber_scheduler_discipline_create)(
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
status RCPR_SYM(psock_fiber_scheduler_disciplined_read_wait_callback_handler)(
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
status RCPR_SYM(psock_fiber_scheduler_disciplined_write_wait_callback_handler)(
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
status RCPR_SYM(psock_idle_fiber_entry)(void* context);

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
status RCPR_SYM(psock_fiber_scheduler_discipline_context_create)(
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
void RCPR_SYM(psock_fiber_scheduler_discipline_set_resource_release)(
    RCPR_SYM(fiber_scheduler_discipline)* disc, RCPR_SYM(resource)* context);

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Ignored for raw buffer reads.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_buffer_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block);

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
status RCPR_SYM(psock_from_buffer_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size);

/**
 * \brief Dummy accept method.  We can't accept from a buffer.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param desc          Pointer to the integer field to hold the accepted
 *                      descriptor.
 * \param addr          The address of the accepted socket.
 * \param addrlen       On input, the max size of the address field; on output,
 *                      the size of the address field.
 *
 * \returns a status code indicating success or failure.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE - accept is unsupported in buffer socks.
 */
status RCPR_SYM(psock_from_buffer_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);

/**
 * \brief Release a psock_from_buffer resource.
 *
 * \param r             Pointer to the psock_from_buffer resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_from_buffer_release)(RCPR_SYM(resource)* r);

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
status RCPR_SYM(psock_ex_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block);

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
status RCPR_SYM(psock_ex_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size);

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
status RCPR_SYM(psock_ex_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);

/**
 * \brief Release a psock_ex resource.
 *
 * \param r             Pointer to the psock_ex resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_ex_release)(RCPR_SYM(resource)* r);

/**
 * \brief Read data from the given \ref psock instance.
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
status RCPR_SYM(psock_br_psock_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block);

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
status RCPR_SYM(psock_br_psock_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size);

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
status RCPR_SYM(psock_br_psock_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_br_psock_sendmsg)(
    RCPR_SYM(psock)* sock, const struct msghdr* msg, int flags);

/**
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_br_psock_recvmsg)(
    RCPR_SYM(psock)* sock, struct msghdr* msg, size_t* len, int flags);

/**
 * \brief Release a psock_br resource.
 *
 * \param r             Pointer to the psock_br resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_br_release)(RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/
#define RCPR_IMPORT_psock_internal \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(psock_from_descriptor) psock_from_descriptor; \
    typedef RCPR_SYM(psock_wrap_async) psock_wrap_async; \
    typedef RCPR_SYM(psock_from_buffer) psock_from_buffer; \
    typedef RCPR_SYM(psock_output_buffer_node) psock_output_buffer_node; \
    typedef RCPR_SYM(psock_ex) psock_ex; \
    typedef RCPR_SYM(psock_br) psock_br; \
    static inline status psock_from_descriptor_read( \
        RCPR_SYM(psock)* w, void* x, size_t* y, bool z) { \
            return RCPR_SYM(psock_from_descriptor_read)(w,x,y,z); } \
    static inline status psock_from_descriptor_write( \
        RCPR_SYM(psock)* x, const void* y, size_t* z) { \
            return RCPR_SYM(psock_from_descriptor_write)(x,y,z); } \
    static inline status psock_from_descriptor_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_from_descriptor_accept)(w,x,y,z); } \
    static inline status psock_from_descriptor_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(psock_from_descriptor_release)(x); } \
    static inline status psock_wrap_async_read( \
        RCPR_SYM(psock)* w, void* x, size_t* y, bool z) { \
            return RCPR_SYM(psock_wrap_async_read)(w,x,y,z); } \
    static inline status psock_wrap_async_write( \
        RCPR_SYM(psock)* x, const void* y, size_t* z) { \
             return RCPR_SYM(psock_wrap_async_write)(x,y,z); } \
    static inline status psock_wrap_async_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_wrap_async_accept)(w,x,y,z); } \
    static inline status psock_fiber_scheduler_discipline_create( \
        RCPR_SYM(fiber_scheduler_discipline)** w, RCPR_SYM(resource)** x, \
        RCPR_SYM(fiber_scheduler)* y, RCPR_SYM(allocator)* z) { \
            return \
                RCPR_SYM(psock_fiber_scheduler_discipline_create)(w,x,y,z); } \
    static inline status \
    psock_fiber_scheduler_disciplined_read_wait_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
          return \
            RCPR_SYM( \
              psock_fiber_scheduler_disciplined_read_wait_callback_handler)( \
                w,x,y,z); } \
    static inline status \
    psock_fiber_scheduler_disciplined_write_wait_callback_handler( \
        void* w, RCPR_SYM(fiber)* x, int y, void* z) { \
          return \
            RCPR_SYM( \
              psock_fiber_scheduler_disciplined_write_wait_callback_handler)( \
                w,x,y,z); } \
    static inline status psock_idle_fiber_entry( \
        void* x) { \
            return RCPR_SYM(psock_idle_fiber_entry)(x); } \
    static inline status psock_fiber_scheduler_discipline_context_create( \
        RCPR_SYM(resource)** x, RCPR_SYM(fiber_scheduler)* y, \
        RCPR_SYM(allocator)* z) { \
            return RCPR_SYM(psock_fiber_scheduler_discipline_context_create)( \
                x,y,z); } \
    static inline void psock_fiber_scheduler_discipline_set_resource_release( \
        RCPR_SYM(fiber_scheduler_discipline)* x, RCPR_SYM(resource)* y) { \
            RCPR_SYM(psock_fiber_scheduler_discipline_set_resource_release)( \
                x,y); } \
    static inline status psock_from_buffer_read( \
        RCPR_SYM(psock)* w, void* x, size_t* y, bool z) { \
            return RCPR_SYM(psock_from_buffer_read)(w,x,y,z); } \
    static inline status psock_from_buffer_write( \
        RCPR_SYM(psock)* x, const void* y, size_t* z) { \
            return RCPR_SYM(psock_from_buffer_write)(x,y,z); } \
    static inline status psock_from_buffer_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_from_buffer_accept)(w,x,y,z); } \
    static inline status psock_from_buffer_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(psock_from_buffer_release)(x); } \
    static inline status psock_from_descriptor_sendmsg( \
        RCPR_SYM(psock)* x, const struct msghdr* y, int z) { \
            return RCPR_SYM(psock_from_descriptor_sendmsg)(x,y,z); } \
    static inline status psock_from_descriptor_recvmsg( \
        RCPR_SYM(psock)* w, struct msghdr* x, size_t* y, int z) { \
            return RCPR_SYM(psock_from_descriptor_recvmsg)(w,x,y,z); } \
    static inline status psock_wrap_async_sendmsg( \
        RCPR_SYM(psock)* x, const struct msghdr* y, int z) { \
            return RCPR_SYM(psock_wrap_async_sendmsg)(x,y,z); } \
    static inline status psock_wrap_async_recvmsg( \
        RCPR_SYM(psock)* w, struct msghdr* x, size_t* y, int z) { \
            return RCPR_SYM(psock_wrap_async_recvmsg)(w,x,y,z); } \
    static inline status psock_ex_read( \
        RCPR_SYM(psock)* w, void* x, size_t* y, bool z) { \
            return RCPR_SYM(psock_ex_read)(w,x,y,z); } \
    static inline status psock_ex_write( \
        RCPR_SYM(psock)* x, const void* y, size_t* z) { \
            return RCPR_SYM(psock_ex_write)(x,y,z); } \
    static inline status psock_ex_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_ex_accept)(w,x,y,z); } \
    static inline status psock_ex_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(psock_ex_release)(x); } \
    static inline status psock_br_psock_read( \
        RCPR_SYM(psock)* w, void* x, size_t* y, bool z) { \
            return RCPR_SYM(psock_br_psock_read)(w,x,y,z); } \
    static inline status psock_br_psock_write( \
        RCPR_SYM(psock)* x, const void* y, size_t* z) { \
            return RCPR_SYM(psock_br_psock_write)(x,y,z); } \
    static inline status psock_br_psock_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_br_psock_accept)(w,x,y,z); } \
    static inline status psock_br_psock_sendmsg( \
        RCPR_SYM(psock)* x, const struct msghdr* y, int z) { \
            return RCPR_SYM(psock_br_psock_sendmsg)(x,y,z); } \
    static inline status psock_br_psock_recvmsg( \
        RCPR_SYM(psock)* w, struct msghdr* x, size_t* y, int z) { \
            return RCPR_SYM(psock_br_psock_recvmsg)(w,x,y,z); } \
    static inline status psock_br_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(psock_br_release)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
