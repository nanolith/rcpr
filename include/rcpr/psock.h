/**
 * \file rcpr/psock.h
 *
 * \brief Process socket I/O library.
 *
 * The purpose of this library is to enable inter-process communication via
 * sockets.  The library is structured so that concerns like encryption, message
 * authentication, compression, and asynchronous I/O can be layered in as
 * needed.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/fiber_fwd.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>
#include <rcpr/uuid.h>
#include <sys/socket.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The psock abstraction enables inter-process communication via a
 * socket, and enables layering of encryption, message authentication,
 * compression, and asynchronous I/O.
 */
typedef struct RCPR_SYM(psock) RCPR_SYM(psock);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref psock instance backed by the given file descriptor.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param descriptor    The file descriptor backing this \ref psock instance.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the descriptor, which will be closed when this resource is
 * released.
 *
 * The \ref psock instance created is assumed to be backed by a blocking stream
 * socket, and any read / write operations on this socket will behave
 * accordingly.  On platforms which support this, \ref psock_create_wrap_async
 * can be called to wrap this \ref psock instance with an asyncronous I/O
 * instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p descriptor must be a valid descriptor for a blocking socket stream.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_from_descriptor)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a, int descriptor);

/**
 * \brief Wrap a \ref psock instance with an async \ref psock instance that
 * transforms reads or writes on the underlying \ref psock with yields to the
 * given \ref fiber_scheduler.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this
 *                      wrapping \ref psock resource.
 * \param fib           The \ref fiber instance that will be using this \ref
 *                      psock instance. Its assigned \ref fiber_scheduler
 *                      instance will be used to yield on any read / write calls
 *                      that would block.  The assigned \ref fiber_scheduler
 *                      instance  must be a disciplined fiber scheduler.
 * \param child         The child \ref psock instance that this \ref psock
 *                      instance wraps.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the wrapped \p child \ref psock, which will be released when
 * this resource is released.
 *
 * It is assumed that the \ref psock wrapper instance created by this call will
 * be accessed from a \ref fiber.  If a read or write fails because
 * it would block, then this \ref fiber yields to the given scheduler with a
 * message indicating that it is yielding on a read or a write for the
 * underlying descriptor.  The scheduler will then resume this \ref fiber when
 * the OS notifies it that the descriptor is again available for read or write.
 *
 * After this call completes successfully, calls to \ref psock utility functions
 * will block the calling fiber if the I/O would normally block.  If multiple
 * fibers are scheduled to run, the scheduler will switch to the next available
 * fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE if the type of psock pointed to by
 *        \p child is not supported for async wrappering. Currently, only
 *        descriptor children are supported.
 *
 * \pre
 *      - \p sock must be a pointer to a pointer to a \ref psock instance
 *        and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p fib must reference a valid \ref fiber instance and must not be
 *        NULL.
 *      - \p fib must be assigned to a disciplined \ref fiber_scheduler
 *        instance.
 *      - \p child must reference a valid \ref psock instance and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_wrap_async)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a,
    RCPR_SYM(fiber)* fib, RCPR_SYM(psock)* child);

/**
 * \brief Create a \ref psock instance backed by a listen socket bound to the
 * given address.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param name          The name to which this socket should be bound.
 * \param namelen       The length of the name address field.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the descriptor, which will be closed when this resource is
 * released.
 *
 * The \ref psock instance created is assumed to be backed by a blocking stream
 * socket, and any read / write operations on this socket will behave
 * accordingly.  On platforms which support this, \ref psock_create_wrap_async
 * can be called to wrap this \ref psock instance with an asyncronous I/O
 * instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p descriptor must be a valid descriptor for a blocking socket stream.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_from_listen_address)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a,
    const struct sockaddr* name, socklen_t namelen);

/**
 * \brief Create a \ref psock instance backed by a given string buffer.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param buffer        The buffer backing this psock instance.
 * \param size          The size of this buffer.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the descriptor, which will be closed when this resource is
 * released.
 *
 * The \ref psock instance created is backed by a string buffer. Reads will
 * start at the beginning of this buffer. Writes will also start at the
 * beginning of this buffer. Reads past the end of the buffer will
 * result in EOF.  Writes past the end of the buffer will extend the buffer to a
 * larger size.  As such, the contents of the buffer are copied to memory. If
 * buffer is NULL, then a new output-only buffer is created.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p buffer must be the given size or NULL.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_from_buffer)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a,
    const char* buffer, size_t size);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_int64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_int64 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a 64-bit
 * integer, which is written in Big Endian order.  No matter the platform of
 * either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int64_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 64-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_int64)(
    RCPR_SYM(psock)* sock, int64_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_uint64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_uint64 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is an unsigned
 * 64-bit integer, which is written in Big Endian order.  No matter the platform
 * of either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint64_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 64-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_uint64)(
    RCPR_SYM(psock)* sock, uint64_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_int32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_int32 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a 32-bit
 * integer, which is written in Big Endian order.  No matter the platform of
 * either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int32_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 32-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_int32)(
    RCPR_SYM(psock)* sock, int32_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_uint32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_uint32 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is an unsigned
 * 32-bit integer, which is written in Big Endian order.  No matter the platform
 * of either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint32_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 32-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_uint32)(
    RCPR_SYM(psock)* sock, uint32_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_int16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_int16 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a 16-bit
 * integer, which is written in Big Endian order.  No matter the platform of
 * either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int16_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 16-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_int16)(
    RCPR_SYM(psock)* sock, int16_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_uint16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_uint16 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is an unsigned
 * 16-bit integer, which is written in Big Endian order.  No matter the platform
 * of either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint16_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 16-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_uint16)(
    RCPR_SYM(psock)* sock, uint16_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_int8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_int8 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a 8-bit
 * integer, which is written in Big Endian order.  No matter the platform of
 * either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int8_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 8-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_int8)(
    RCPR_SYM(psock)* sock, int8_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_uint8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_uint8 method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is an unsigned
 * 8-bit integer, which is written in Big Endian order.  No matter the platform
 * of either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint8_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 8-bit integer value read from the
 *        socket and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_uint8)(
    RCPR_SYM(psock)* sock, uint8_t* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_bool.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_bool method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a boolean
 * value. No matter the platform of either peer, the value will be converted to
 * or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid bool variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the boolean value read from the socket
 *        and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_bool)(
    RCPR_SYM(psock)* sock, bool* val);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_string.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      value.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.  On success, this pointer is updated to a
 *                      string value that is owned by the caller and must be
 *                      released to the allocator when no longer needed.
 * \param length        Pointer to a variable to be set to the length of this
 *                      string on success.
 *
 * The \ref psock_write_boxed_string method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a C-string
 * value.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p a must be a pointer to a valid \ref allocator instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid C-string variable and must not be
 *        NULL.
 *      - \p length must be a pointer to a size_t value and must not be NULL.
 *
 * \post
 *      - On success, \p val is set to the C-string value read from the socket
 *        and unboxed.
 *      - On success, \p length is set to the length of the C-string.
 *      - On failure, \p val is unchanged and an error status is returned.
 *      - On failure, \p length is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_string)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, char** val, size_t* length);

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      value.
 * \param data          Pointer to the value to be set based on a successful I/O
 *                      operation.  On success, this pointer is updated to a
 *                      data value that is owned by the caller and must be
 *                      released to the allocator when no longer needed.
 * \param data_size     Pointer to a variable to be set to the length of this
 *                      data on success.
 *
 * The \ref psock_write_boxed_data method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a raw data
 * value.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p a must be a pointer to a valid \ref allocator instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid pointer and must not be NULL.
 *      - \p data_size must be a pointer to a size_t value and must not be NULL.
 *
 * \post
 *      - On success, \p data is set to a buffer containing the data read from
 *        the socket and unboxed.
 *      - On success, \p data_size is set to the length of the data buffer.
 *      - On failure, \p data is unchanged and an error status is returned.
 *      - On failure, \p data_size is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_data)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, void** data,
    size_t* data_size);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_int64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int64_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_int64 method.  This boxed packet
 * contains a tag noting that the following value is a 64-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_int64)(
    RCPR_SYM(psock)* sock, int64_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_uint64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint64_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_uint64 method.  This boxed packet
 * contains a tag noting that the following value is a 64-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_uint64)(
    RCPR_SYM(psock)* sock, uint64_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_int32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int32_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_int32 method.  This boxed packet
 * contains a tag noting that the following value is a 32-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_int32)(
    RCPR_SYM(psock)* sock, int32_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_uint32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint32_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_uint32 method.  This boxed packet
 * contains a tag noting that the following value is a 32-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_uint32)(
    RCPR_SYM(psock)* sock, uint32_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_int16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int16_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_int16 method.  This boxed packet
 * contains a tag noting that the following value is a 16-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_int16)(
    RCPR_SYM(psock)* sock, int16_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_uint16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint16_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_uint16 method.  This boxed packet
 * contains a tag noting that the following value is a 16-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_uint16)(
    RCPR_SYM(psock)* sock, uint16_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_int8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int8_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_int8 method.  This boxed packet
 * contains a tag noting that the following value is a 8-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_int8)(
    RCPR_SYM(psock)* sock, int8_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_uint8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint8_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_uint8 method.  This boxed packet
 * contains a tag noting that the following value is a 8-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_uint8)(
    RCPR_SYM(psock)* sock, uint8_t val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_bool.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A bool value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_bool method.  This boxed packet
 * contains a tag noting that the following value is a boolean value.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_bool)(
    RCPR_SYM(psock)* sock, bool val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_string.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A C-string value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_string method.  This boxed packet
 * contains a tag noting that the following value is a C-string value.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a valid C-string pointer.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_string)(
    RCPR_SYM(psock)* sock, const char* val);

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param data          A raw data value to be written to the socket.
 * \param data_size     The size of the data to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_data method.  This boxed packet
 * contains a tag noting that the following value is a raw data packet.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a buffer that is \p data_size bytes in
 *        length.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_data)(
    RCPR_SYM(psock)* sock, const void* data, size_t data_size);

/**
 * \brief Attempt to read up to \p data_size bytes from the psock instance. This
 * function will return fewer bytes (updating \p data_size accordingly) if no
 * more bytes are currently available.  In this case, this function will return
 * \ref ERROR_PSOCK_READ_WOULD_BLOCK, and it's up to the caller to decide
 * whether to block on more bytes by calling \ref psock_read_block. If the
 * descriptor reaches a natural end, such as the end of a file,
 * \ref STATUS_SUCCESS will be returned.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param data          Pointer to a buffer that can accept up to \p data_size
 *                      bytes.  This must be a valid buffer.
 * \param data_size     Size of the data to read. Set to the number of bytes to
 *                      read by the caller, and updated to the number of bytes
 *                      actually read by the successful execution of this
 *                      function.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_PSOCK_READ_WOULD_BLOCK if reading more data would block.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid buffer that is at least
 *        \p data_size bytes in length.
 *      - \p data_size must be a pointer to a valid size argument, set to the
 *        size of the \p data buffer.
 *
 * \post
 *      - On success, \p data contains the bytes written, and \p data_size is
 *        set to the number of bytes written.
 *      - On failure, \p data is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw)(
    RCPR_SYM(psock)* sock, void* data, size_t* data_size);

/**
 * \brief Block until a read is available.  This is used in conjunction with
 * \ref psock_read_raw in order to read arbitrary length data from a \ref psock
 * instance.
 *
 * \param sock          Pointer to the \ref psock pointer on which to block.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE if this \ref psock instance is not a
 *        non-blocking instance.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *
 * \post
 *      - On success, data is available to read on this \ref psock instance, or
 *        the peer has closed this \ref psock instance, or a connection error on
 *        this \ref psock instance has occurred.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_block)(RCPR_SYM(psock)* sock);

/**
 * \brief Block until the socket is available for writing.
 *
 * \param sock          Pointer to the \ref psock pointer on which to block.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE if this \ref psock instance is not a
 *        non-blocking instance.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *
 * \post
 *      - On success, this \ref psock instance is available for write, or
 *        the peer has closed this \ref psock instance, or a connection error on
 *        this \ref psock instance has occurred.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_block)(RCPR_SYM(psock)* sock);

/**
 * \brief Read a raw value from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_raw_int64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_int64 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int64_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 64-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_int64)(
    RCPR_SYM(psock)* sock, int64_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_raw_uint64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_uint64 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint64_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 64-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_uint64)(
    RCPR_SYM(psock)* sock, uint64_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_raw_int32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_int32 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int32_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 32-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_int32)(
    RCPR_SYM(psock)* sock, int32_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_uint32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_uint32 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint32_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 32-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_uint32)(
    RCPR_SYM(psock)* sock, uint32_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_int16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_int16 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int16_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 16-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_int16)(
    RCPR_SYM(psock)* sock, int16_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_uint16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_uint16 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint16_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 16-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_uint16)(
    RCPR_SYM(psock)* sock, uint16_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_int8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_int8 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid int8_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 8-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_int8)(
    RCPR_SYM(psock)* sock, int8_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_uint8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_uint8 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint8_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 8-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_uint8)(
    RCPR_SYM(psock)* sock, uint8_t* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_bool.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_bool method writes a raw value to the socket, which
 * is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  No matter the platform
 * of either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid bool variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the boolean value read from the socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_bool)(
    RCPR_SYM(psock)* sock, bool* val);

/**
 * \brief Read a raw value from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_raw_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      value.
 * \param data          Pointer to the value to be set based on a successful I/O
 *                      operation.  On success, this pointer is updated to a
 *                      data value that is owned by the caller and must be
 *                      released to the allocator when no longer needed.
 * \param data_size     Size of the data to read.
 *
 * The \ref psock_write_raw_data method writes a raw data value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw data value is written and read as-is, and requires coordination with the
 * peer to determine the correct size to read or write.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p a must be a pointer to a valid \ref allocator instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid pointer and must not be NULL.
 *
 * \post
 *      - On success, \p data is set to a buffer containing the data read from
 *        the socket.
 *      - On failure, \p data is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_data)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, void** data,
    size_t data_size);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_int64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int64_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_int64 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_int64)(
    RCPR_SYM(psock)* sock, int64_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_raw_uint64.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint64_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_uint64 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_uint64)(
    RCPR_SYM(psock)* sock, uint64_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_int32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int32_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_int32 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_int32)(
    RCPR_SYM(psock)* sock, int32_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_uint32.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint32_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_uint32 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_uint32)(
    RCPR_SYM(psock)* sock, uint32_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_int16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int16_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_int16 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_int16)(
    RCPR_SYM(psock)* sock, int16_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_uint16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint16_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_uint16 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_uint16)(
    RCPR_SYM(psock)* sock, uint16_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_int8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int8_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_int8 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_int8)(
    RCPR_SYM(psock)* sock, int8_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_uint8.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint8_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_uint8 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_uint8)(
    RCPR_SYM(psock)* sock, uint8_t val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_bool.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A bool value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_bool method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_bool)(
    RCPR_SYM(psock)* sock, bool val);

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param data          A raw data value to be written to the socket.
 * \param data_size     The size of the data to be written to the socket.
 *
 * This method writes a raw data value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_data method.  This raw data value
 * is just the value, so care must be used to synchronize communication between
 * the two peers in order to coordinate a read of this raw data and its size.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a buffer that is \p data_size bytes in
 *        length.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_data)(
    RCPR_SYM(psock)* sock, const void* data, size_t data_size);

/**
 * \brief Accept a socket from a listen socket \ref psock instance.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param desc          Pointer to the integer variable to receive the socket
 *                      descriptor.
 * \param addr          Pointer to a socket address structure to receive the
 *                      peer's address.
 * \param addrlen       Pointer to a size for the socket address, which will be
 *                      updated with the size of socket address from this accept
 *                      operation.
 *
 * This method accepts a socket from a bound listen socket, created with
 * \ref psock_create_from_listen_address.  This socket is from a peer who
 * connected to the address and port specified by that constructor.  This
 * descriptor is a RAW RESOURCE that is not yet backed by a resource.  It must
 * be closed via \ref close or passed to \ref psock_create_from_descriptor to
 * turn it into a proper \ref resource.  The reason for making this a RAW
 * RESOURCE is historic and based on existing socket programming patterns.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p desc must be a pointer to a valid integer variable and must not be
 *        NULL.
 *      - \p addr must be a pointer to a socket address structure and must not
 *        be NULL.
 *      - \p addrlen must be a pointer to a socket length field set to the size
 *        of \p addr and must not be NULL.
 * \post
 *      - on success, \p desc is set to a socket descriptor that must either be
 *        closed or attached to a psock instance.
 *      - on success, \p addr and \p addrlen are set to the peer's address.
 *      - on failure, no field is updated.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_accept)(
    RCPR_SYM(psock)* sock, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref psock instance, return the resource handle for this
 * \ref psock instance.
 *
 * \param sock          The \ref psock instance from which the resource handle
 *                      is returned.
 *
 * \returns the resource handle for this \ref psock instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(psock_resource_handle)(
    RCPR_SYM(psock)* sock);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref psock property.
 *
 * \param sock          The \ref psock instance to be verified.
 *
 * \returns true if the \ref psock instance is valid.
 */
bool
RCPR_SYM(prop_psock_valid)(
    const RCPR_SYM(psock)* sock);

/******************************************************************************/
/* Start of support types.                                                    */
/******************************************************************************/

enum psock_boxed_type
{
    PSOCK_BOXED_TYPE_INT64                      =   0x00000010,
    PSOCK_BOXED_TYPE_UINT64                     =   0x00000011,
    PSOCK_BOXED_TYPE_INT32                      =   0x00000012,
    PSOCK_BOXED_TYPE_UINT32                     =   0x00000013,
    PSOCK_BOXED_TYPE_INT16                      =   0x00000014,
    PSOCK_BOXED_TYPE_UINT16                     =   0x00000015,
    PSOCK_BOXED_TYPE_INT8                       =   0x00000016,
    PSOCK_BOXED_TYPE_UINT8                      =   0x00000017,
    PSOCK_BOXED_TYPE_BOOL                       =   0x00000018,
    PSOCK_BOXED_TYPE_STRING                     =   0x00000020,
    PSOCK_BOXED_TYPE_DATA                       =   0x00000022,
};

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_psock_as(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(psock) sym ## _ ## psock; \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_create_from_descriptor( \
        RCPR_SYM(psock)** x, RCPR_SYM(allocator)* y, int z) { \
            return RCPR_SYM(psock_create_from_descriptor)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_create_wrap_async( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        RCPR_SYM(fiber)* y, RCPR_SYM(psock)* z) { \
            return RCPR_SYM(psock_create_wrap_async)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_create_from_listen_address( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const struct sockaddr* y, socklen_t z) { \
            return RCPR_SYM(psock_create_from_listen_address)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_create_from_buffer( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const char* y, size_t z) { \
            return RCPR_SYM(psock_create_from_buffer)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_int64( \
        RCPR_SYM(psock)* x, int64_t* y) { \
            return RCPR_SYM(psock_read_boxed_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_uint64( \
        RCPR_SYM(psock)* x, uint64_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_int32( \
        RCPR_SYM(psock)* x, int32_t* y) { \
            return RCPR_SYM(psock_read_boxed_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_uint32( \
        RCPR_SYM(psock)* x, uint32_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_int16( \
        RCPR_SYM(psock)* x, int16_t* y) { \
            return RCPR_SYM(psock_read_boxed_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_uint16( \
        RCPR_SYM(psock)* x, uint16_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_int8( \
        RCPR_SYM(psock)* x, int8_t* y) { \
            return RCPR_SYM(psock_read_boxed_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_uint8( \
        RCPR_SYM(psock)* x, uint8_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_bool( \
        RCPR_SYM(psock)* x, bool* y) { \
            return RCPR_SYM(psock_read_boxed_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_string( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, char** y, size_t* z) { \
            return RCPR_SYM(psock_read_boxed_string)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_boxed_data( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t* z) { \
            return RCPR_SYM(psock_read_boxed_data)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_int64( \
        RCPR_SYM(psock)* x, int64_t y) { \
            return RCPR_SYM(psock_write_boxed_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_uint64( \
        RCPR_SYM(psock)* x, uint64_t y) { \
            return RCPR_SYM(psock_write_boxed_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_int32( \
        RCPR_SYM(psock)* x, int32_t y) { \
            return RCPR_SYM(psock_write_boxed_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_uint32( \
        RCPR_SYM(psock)* x, uint32_t y) { \
            return RCPR_SYM(psock_write_boxed_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_int16( \
        RCPR_SYM(psock)* x, int16_t y) { \
            return RCPR_SYM(psock_write_boxed_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_uint16( \
        RCPR_SYM(psock)* x, uint16_t y) { \
            return RCPR_SYM(psock_write_boxed_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_int8( \
        RCPR_SYM(psock)* x, int8_t y) { \
            return RCPR_SYM(psock_write_boxed_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_uint8( \
        RCPR_SYM(psock)* x, uint8_t y) { \
            return RCPR_SYM(psock_write_boxed_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_bool( \
        RCPR_SYM(psock)* x, bool y) { \
            return RCPR_SYM(psock_write_boxed_bool)(x, y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_string( \
        RCPR_SYM(psock)* x, const char* y) { \
            return RCPR_SYM(psock_write_boxed_string)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_boxed_data( \
        RCPR_SYM(psock)* x, const void* y, size_t z) { \
            return RCPR_SYM(psock_write_boxed_data)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw( \
        RCPR_SYM(psock)* x, void* y, size_t* z) { \
            return RCPR_SYM(psock_read_raw)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_block( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_read_block)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_block( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_write_block)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_int64( \
        RCPR_SYM(psock)* x, int64_t* y) { \
            return RCPR_SYM(psock_read_raw_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_uint64( \
        RCPR_SYM(psock)* x, uint64_t* y) { \
            return RCPR_SYM(psock_read_raw_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_int32( \
        RCPR_SYM(psock)* x, int32_t* y) { \
            return RCPR_SYM(psock_read_raw_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_uint32( \
        RCPR_SYM(psock)* x, uint32_t* y) { \
            return RCPR_SYM(psock_read_raw_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_int16( \
        RCPR_SYM(psock)* x, int16_t* y) { \
            return RCPR_SYM(psock_read_raw_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_uint16( \
        RCPR_SYM(psock)* x, uint16_t* y) { \
            return RCPR_SYM(psock_read_raw_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_int8( \
        RCPR_SYM(psock)* x, int8_t* y) { \
            return RCPR_SYM(psock_read_raw_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_uint8( \
        RCPR_SYM(psock)* x, uint8_t* y) { \
            return RCPR_SYM(psock_read_raw_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_bool( \
        RCPR_SYM(psock)* x, bool* y) { \
            return RCPR_SYM(psock_read_raw_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_read_raw_data( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(psock_read_raw_data)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_int64( \
        RCPR_SYM(psock)* x, int64_t y) { \
            return RCPR_SYM(psock_write_raw_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_uint64( \
        RCPR_SYM(psock)* x, uint64_t y) { \
            return RCPR_SYM(psock_write_raw_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_int32( \
        RCPR_SYM(psock)* x, int32_t y) { \
            return RCPR_SYM(psock_write_raw_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_uint32( \
        RCPR_SYM(psock)* x, uint32_t y) { \
            return RCPR_SYM(psock_write_raw_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_int16( \
        RCPR_SYM(psock)* x, int16_t y) { \
            return RCPR_SYM(psock_write_raw_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_uint16( \
        RCPR_SYM(psock)* x, uint16_t y) { \
            return RCPR_SYM(psock_write_raw_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_int8( \
        RCPR_SYM(psock)* x, int8_t y) { \
            return RCPR_SYM(psock_write_raw_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_uint8( \
        RCPR_SYM(psock)* x, uint8_t y) { \
            return RCPR_SYM(psock_write_raw_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_bool( \
        RCPR_SYM(psock)* x, bool y) { \
            return RCPR_SYM(psock_write_raw_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_write_raw_data( \
        RCPR_SYM(psock)* x, const void* y, size_t z) { \
            return RCPR_SYM(psock_write_raw_data)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## psock_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_accept)(w,x,y,z); } \
    static inline RCPR_SYM(resource)* \
    sym ## _ ## psock_resource_handle( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_resource_handle)(x); } \
    static inline bool \
    sym ## _ ## prop_psock_valid( \
        const RCPR_SYM(psock)* x) { \
            return RCPR_SYM(prop_psock_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_psock \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(psock) psock; \
    static inline status FN_DECL_MUST_CHECK psock_create_from_descriptor( \
        RCPR_SYM(psock)** x, RCPR_SYM(allocator)* y, int z) { \
            return RCPR_SYM(psock_create_from_descriptor)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_create_wrap_async( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        RCPR_SYM(fiber)* y, RCPR_SYM(psock)* z) { \
            return RCPR_SYM(psock_create_wrap_async)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_create_from_listen_address( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const struct sockaddr* y, socklen_t z) { \
            return RCPR_SYM(psock_create_from_listen_address)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_create_from_buffer( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const char* y, size_t z) { \
            return RCPR_SYM(psock_create_from_buffer)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_int64( \
        RCPR_SYM(psock)* x, int64_t* y) { \
            return RCPR_SYM(psock_read_boxed_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_uint64( \
        RCPR_SYM(psock)* x, uint64_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_int32( \
        RCPR_SYM(psock)* x, int32_t* y) { \
            return RCPR_SYM(psock_read_boxed_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_uint32( \
        RCPR_SYM(psock)* x, uint32_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_int16( \
        RCPR_SYM(psock)* x, int16_t* y) { \
            return RCPR_SYM(psock_read_boxed_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_uint16( \
        RCPR_SYM(psock)* x, uint16_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_int8( \
        RCPR_SYM(psock)* x, int8_t* y) { \
            return RCPR_SYM(psock_read_boxed_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_uint8( \
        RCPR_SYM(psock)* x, uint8_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_bool( \
        RCPR_SYM(psock)* x, bool* y) { \
            return RCPR_SYM(psock_read_boxed_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_string( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, char** y, size_t* z) { \
            return RCPR_SYM(psock_read_boxed_string)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_read_boxed_data( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t* z) { \
            return RCPR_SYM(psock_read_boxed_data)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_int64( \
        RCPR_SYM(psock)* x, int64_t y) { \
            return RCPR_SYM(psock_write_boxed_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_uint64( \
        RCPR_SYM(psock)* x, uint64_t y) { \
            return RCPR_SYM(psock_write_boxed_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_int32( \
        RCPR_SYM(psock)* x, int32_t y) { \
            return RCPR_SYM(psock_write_boxed_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_uint32( \
        RCPR_SYM(psock)* x, uint32_t y) { \
            return RCPR_SYM(psock_write_boxed_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_int16( \
        RCPR_SYM(psock)* x, int16_t y) { \
            return RCPR_SYM(psock_write_boxed_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_uint16( \
        RCPR_SYM(psock)* x, uint16_t y) { \
            return RCPR_SYM(psock_write_boxed_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_int8( \
        RCPR_SYM(psock)* x, int8_t y) { \
            return RCPR_SYM(psock_write_boxed_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_uint8( \
        RCPR_SYM(psock)* x, uint8_t y) { \
            return RCPR_SYM(psock_write_boxed_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_bool( \
        RCPR_SYM(psock)* x, bool y) { \
            return RCPR_SYM(psock_write_boxed_bool)(x, y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_string( \
        RCPR_SYM(psock)* x, const char* y) { \
            return RCPR_SYM(psock_write_boxed_string)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_boxed_data( \
        RCPR_SYM(psock)* x, const void* y, size_t z) { \
            return RCPR_SYM(psock_write_boxed_data)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw( \
        RCPR_SYM(psock)* x, void* y, size_t* z) { \
            return RCPR_SYM(psock_read_raw)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_read_block( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_read_block)(x); } \
    static inline status FN_DECL_MUST_CHECK psock_write_block( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_write_block)(x); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_int64( \
        RCPR_SYM(psock)* x, int64_t* y) { \
            return RCPR_SYM(psock_read_raw_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_uint64( \
        RCPR_SYM(psock)* x, uint64_t* y) { \
            return RCPR_SYM(psock_read_raw_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_int32( \
        RCPR_SYM(psock)* x, int32_t* y) { \
            return RCPR_SYM(psock_read_raw_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_uint32( \
        RCPR_SYM(psock)* x, uint32_t* y) { \
            return RCPR_SYM(psock_read_raw_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_int16( \
        RCPR_SYM(psock)* x, int16_t* y) { \
            return RCPR_SYM(psock_read_raw_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_uint16( \
        RCPR_SYM(psock)* x, uint16_t* y) { \
            return RCPR_SYM(psock_read_raw_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_int8( \
        RCPR_SYM(psock)* x, int8_t* y) { \
            return RCPR_SYM(psock_read_raw_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_uint8( \
        RCPR_SYM(psock)* x, uint8_t* y) { \
            return RCPR_SYM(psock_read_raw_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_bool( \
        RCPR_SYM(psock)* x, bool* y) { \
            return RCPR_SYM(psock_read_raw_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_read_raw_data( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(psock_read_raw_data)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_int64( \
        RCPR_SYM(psock)* x, int64_t y) { \
            return RCPR_SYM(psock_write_raw_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_uint64( \
        RCPR_SYM(psock)* x, uint64_t y) { \
            return RCPR_SYM(psock_write_raw_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_int32( \
        RCPR_SYM(psock)* x, int32_t y) { \
            return RCPR_SYM(psock_write_raw_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_uint32( \
        RCPR_SYM(psock)* x, uint32_t y) { \
            return RCPR_SYM(psock_write_raw_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_int16( \
        RCPR_SYM(psock)* x, int16_t y) { \
            return RCPR_SYM(psock_write_raw_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_uint16( \
        RCPR_SYM(psock)* x, uint16_t y) { \
            return RCPR_SYM(psock_write_raw_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_int8( \
        RCPR_SYM(psock)* x, int8_t y) { \
            return RCPR_SYM(psock_write_raw_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_uint8( \
        RCPR_SYM(psock)* x, uint8_t y) { \
            return RCPR_SYM(psock_write_raw_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_bool( \
        RCPR_SYM(psock)* x, bool y) { \
            return RCPR_SYM(psock_write_raw_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK psock_write_raw_data( \
        RCPR_SYM(psock)* x, const void* y, size_t z) { \
            return RCPR_SYM(psock_write_raw_data)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK psock_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_accept)(w,x,y,z); } \
    static inline RCPR_SYM(resource)* psock_resource_handle( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_resource_handle)(x); } \
    static inline bool prop_psock_valid( \
        const RCPR_SYM(psock)* x) { \
            return RCPR_SYM(prop_psock_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
