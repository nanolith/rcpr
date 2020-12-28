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
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/fiber_fwd.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward decls */
struct psock;

/**
 * \brief The psock abstraction enables inter-process communication via a
 * socket, and enables layering of encryption, message authentication,
 * compression, and asynchronous I/O.
 */
typedef struct psock psock;

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
psock_create_from_descriptor(
    psock** sock, allocator* a, int descriptor);

/**
 * \brief Wrap a \ref psock instance with an async \ref psock instance that
 * transforms reads or writes on the underlying \ref psock with yields to the
 * scheduler for the given \ref fiber.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.  This pointer should be set to the
 *                      \ref psock instance to wrap when this function is
 *                      called.
 * \param a             Pointer to the allocator to use for creating this
 *                      wrapping \ref psock resource.
 * \param f             The \ref fiber to yield on a read / write call that
 *                      would block.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the wrapped \ref psock, which will be released when this
 * resource is released.
 *
 * It is assumed that the \ref psock wrapper instance created by this call will
 * be accessed from the given \p f \ref fiber.  If a read or write fails because
 * it would block, then this \ref fiber is yielded to the scheduler with a
 * message indicating that it is yielding on a read or a write for the
 * underlying descriptor.  The scheduler will then resume this \ref fiber when
 * the OS notifies it that the descriptor is again available for read or write.
 *
 * After this call completes successfully, the \p f \ref fiber can be executed,
 * assuming that somewhere in its context structure, this \ref psock wrapper
 * will be available to it.  The specifics of this mechanism is beyond the scope
 * of this function.  Consult documentation on \ref fiber and \ref
 * fiber_scheduler for more details.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must be a pointer to a pointer to a valid \ref psock instance
 *        and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p f must reference a valid \ref fiber and must not be NULL.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
psock_create_wrap_async(
    psock** sock, allocator* a, fiber* f);

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
psock_read_boxed_int64(
    psock* sock, int64_t* val);

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
psock_read_boxed_uint64(
    psock* sock, uint64_t* val);

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
psock_read_boxed_int32(
    psock* sock, int32_t* val);

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
psock_read_boxed_uint32(
    psock* sock, uint32_t* val);

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
psock_read_boxed_int16(
    psock* sock, int16_t* val);

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
psock_read_boxed_uint16(
    psock* sock, uint16_t* val);

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
psock_read_boxed_int8(
    psock* sock, int8_t* val);

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
psock_read_boxed_uint8(
    psock* sock, uint8_t* val);

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
psock_read_boxed_bool(
    psock* sock, bool* val);

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
psock_read_boxed_string(
    psock* sock, allocator* a, char** val, size_t* length);

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
psock_read_boxed_data(
    psock* sock, allocator* a, void** data, size_t* data_size);

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
psock_write_boxed_int64(
    psock* sock, int64_t val);

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
psock_write_boxed_uint64(
    psock* sock, uint64_t val);

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
psock_write_boxed_int32(
    psock* sock, int32_t val);

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
psock_write_boxed_uint32(
    psock* sock, uint32_t val);

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
psock_write_boxed_int16(
    psock* sock, int16_t val);

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
psock_write_boxed_uint16(
    psock* sock, uint16_t val);

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
psock_write_boxed_int8(
    psock* sock, int8_t val);

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
psock_write_boxed_uint8(
    psock* sock, uint8_t val);

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
psock_write_boxed_bool(
    psock* sock, bool val);

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
psock_write_boxed_string(
    psock* sock, const char* val);

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
psock_write_boxed_data(
    psock* sock, const void* data, size_t data_size);

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
psock_read_raw_int64(
    psock* sock, int64_t* val);

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
psock_read_raw_uint64(
    psock* sock, uint64_t* val);

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
psock_read_raw_int32(
    psock* sock, int32_t* val);

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
psock_read_raw_uint32(
    psock* sock, uint32_t* val);

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
psock_read_raw_int16(
    psock* sock, int16_t* val);

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
psock_read_raw_uint16(
    psock* sock, uint16_t* val);

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
psock_read_raw_int8(
    psock* sock, int8_t* val);

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
psock_read_raw_uint8(
    psock* sock, uint8_t* val);

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
psock_read_raw_bool(
    psock* sock, bool* val);

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
psock_read_raw_data(
    psock* sock, allocator* a, void** data, size_t data_size);

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
psock_write_raw_int64(
    psock* sock, int64_t val);

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
psock_write_raw_uint64(
    psock* sock, uint64_t val);

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
psock_write_raw_int32(
    psock* sock, int32_t val);

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
psock_write_raw_uint32(
    psock* sock, uint32_t val);

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
psock_write_raw_int16(
    psock* sock, int16_t val);

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
psock_write_raw_uint16(
    psock* sock, uint16_t val);

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
psock_write_raw_int8(
    psock* sock, int8_t val);

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
psock_write_raw_uint8(
    psock* sock, uint8_t val);

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
psock_write_raw_bool(
    psock* sock, bool val);

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
psock_write_raw_data(
    psock* sock, void* data, size_t data_size);

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
resource* psock_resource_handle(psock* sock);

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
bool prop_psock_valid(const psock* sock);

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

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/