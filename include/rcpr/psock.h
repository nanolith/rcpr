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
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
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

/**
 * \brief The psock buffered reader adapter provides a buffered reading
 * experience for a psock instance. Among other things, this provides the \ref
 * psock_br_get_line and \ref psock_br_get_line_ex functions, allowing for lines
 * to be read from the socket. This buffered reader also creates a wrapped psock
 * instance, which can be accessed from the buffered reader instance by calling
 * \ref psock_br_psock_adapter. However, this adapter does not take ownership of
 * the underlying psock instance; this ownership is maintained by the caller. It
 * is possible to stack the provided adapter with other adapters, but the
 * buffered reader adapter should only be stacked with other adapters and not
 * with full wrapped psock interfaces, as these take ownership of the adapted
 * psock instance, which is not allowed.
 * Once the buffered reader instance has been used, direct reads on the
 * underlying psock instance should not be performed as they will bypass the
 * buffer in the adapter. Instead, direct reads should be performed using the
 * psock instance returned by \ref psock_br_psock_adapter, as these will allow
 * any function that takes a psock instance to read the same buffered input.
 */
typedef struct RCPR_SYM(psock_br) RCPR_SYM(psock_br);

/**
 * \brief Read function type for a user psock.
 *
 * \param sock          The socket instance that is being read.
 * \param ctx           The user context for this instance.
 * \param data          Pointer to the buffer to receive data from this read
 *                      operation.
 * \param size          Pointer to the size to be read, updated with the number
 *                      of bytes actually read.
 * \param block         Set to true if this read should block until all bytes
 *                      are read, or false if it should return early if reading
 *                      extra bytes would block.
 *
 * \note This function type can be used by the caller to produce a special
 * user-defined \ref psock instance. The context is an opaque type that the user
 * provides during creation and that is passed to all user functions.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid buffer that is at least \p size
 *        bytes in length.
 *      - \p size must be a pointer to a valid size argument, set to the size of
 *        the \p data buffer.
 *
 * \post
 *      - On success, \p data contains the bytes read, and \p size is set to the
 *        number of bytes read.
 *      - On failure, \p data is unchanged and an error status is returned.
 */
typedef status (*RCPR_SYM(psock_read_fn))(
    RCPR_SYM(psock)* sock, void* ctx, void* data, size_t* size, bool block);

/**
 * \brief Write function type for a user psock.
 *
 * \param sock          The socket instance that is being written.
 * \param ctx           The user context for this instance.
 * \param data          Pointer to the buffer to write to the socket instance.
 * \param size          Pointer to the size to be written, updated with the
 *                      number of bytes actually written.
 *
 * \note This function type can be used by the caller to produce a special
 * user-defined \ref psock instance. The context is an opaque type that the user
 * provides during creation and that is passed to all user functions.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid buffer that is at least \p size
 *        bytes in length.
 *      - \p size must be a pointer to a valid size argument, set to the size of
 *        the \p data buffer.
 *
 * \post
 *      - On success, \p data is written to the socket, and \p size is set to
 *        the number of bytes written.
 *      - On failure, an error status is returned.
 */
typedef status (*RCPR_SYM(psock_write_fn))(
        RCPR_SYM(psock)* sock, void* ctx, const void* data, size_t* size);

/**
 * \brief Accept function type for a user psock.
 *
 * \param sock          The socket instance for accepting a socket.
 * \param ctx           The user context for this instance.
 * \param desc          Pointer to receive the socket descriptor on success.
 * \param addr          Pointer to receive the peer socket address on success.
 * \param addrlen       Pointer to receive the peer socket address length on
 *                      success. It should be set to the maximum socket address
 *                      length supported.
 *
 * \note This function type can be used by the caller to produce a special
 * user-defined \ref psock instance. The context is an opaque type that the user
 * provides during creation and that is passed to all user functions.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p desc must be a pointer to a valid descriptor to receive a socket
 *        descriptor on success.
 *      - \p addr must be a pointer to a valid sockaddr struct to receive the
 *        peer socket address on success.
 *      - \p addrlen must be a pointer to a socket length variable set to the
 *        size of the address struct and set to the size of the socket address
 *        on success.
 *
 * \post
 *      - On success, \p data is written to the socket, and \p size is set to
 *        the number of bytes written.
 *      - On failure, an error status is returned.
 */
typedef status (*RCPR_SYM(psock_accept_fn))(
        RCPR_SYM(psock)* sock, void* ctx, int* desc, struct sockaddr* addr,
        socklen_t* addrlen);

/**
 * \brief Release function type for a user psock.
 *
 * \param sock          The socket instance being released.
 * \param ctx           The user context for this instance.
 *
 * \note This function type can be used by the caller to produce a special
 * user-defined \ref psock instance. The context is an opaque type that the user
 * provides during creation and that is passed to all user functions.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *
 * \post
 *      - On success, user-specific release code has been executed.
 *      - On failure, an error status is returned.
 */
typedef status (*RCPR_SYM(psock_release_fn))(
        RCPR_SYM(psock)* sock, void* ctx);

/**
 * \brief Send a message over a user psock.
 *
 * This method roughly corresponds to the POSIX sendmsg function.
 *
 * \param sock          The socket instance for this operation.
 * \param ctx           The user context for this instance.
 * \param msg           The message to send.
 * \param flags         The flags for this operation.
 *
 * \note This function type can be used by the caller to produce a special
 * user-defined \ref psock instance. The context is an opaque type that the user
 * provides during creation and that is passed to all user functions.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p msg must be a pointer to a valid message structure as per the
 *        sendmsg specification.
 *      - \p flags must hold flags relevant to a sendmsg call.
 *
 * \post
 *      - On success, \p msg is written to the socket using the given flags.
 *      - On failure, an error status is returned.
 */
typedef status (*RCPR_SYM(psock_sendmsg_fn))(
        RCPR_SYM(psock)* sock, void* ctx, const struct msghdr* msg, int flags);

/**
 * \brief The \ref psock_vtable structure provides a virtual method interface
 * for overriding psock functions.
 *
 * Virtual tables provide an organized way to group virtual functions that can
 * be hardened against heap attacks. When runtime checking is enabled, calls
 * into a vtable will be checked to ensure that the vtable pointer points to a
 * table in the read-only vtable segment.
 */
typedef struct RCPR_SYM(psock_vtable) RCPR_SYM(psock_vtable);
struct RCPR_SYM(psock_vtable)
{
    RCPR_SYM(resource_vtable) hdr;
    RCPR_SYM(psock_read_fn) read_fn;
    RCPR_SYM(psock_write_fn) write_fn;
    RCPR_SYM(psock_accept_fn) accept_fn;
    RCPR_SYM(psock_release_fn) release_fn;
};

/******************************************************************************/
/* Start of support types.                                                    */
/******************************************************************************/

enum RCPR_SYM(psock_boxed_type)
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

typedef enum RCPR_SYM(psock_boxed_type) RCPR_SYM(psock_boxed_type);

enum RCPR_SYM(socket_type)
{
    PSOCK_SOCKET_TYPE_STREAM            = 0x0001,
    PSOCK_SOCKET_TYPE_DATAGRAM          = 0x0002,
    PSOCK_SOCKET_TYPE_OTHER             = 0x0003,
};

typedef enum RCPR_SYM(socket_type) RCPR_SYM(socket_type);

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
 * \brief Create a \ref psock instance connected to the peer address described
 * by the given hostname and port.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param hostname      The hostname for the connection.
 * \param port          The port.
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
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p hostname must be an ASCII UTF-8 ASCII-Z terminated string.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_from_hostname_and_port)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a,
    const char* hostname, unsigned int port);

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

/**
 * \brief Create a \ref psock_br instance backed by the given \ref psock
 * instance.
 *
 * \param br            Pointer to the \ref psock_br pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock_br resource.
 * \param sock          The \ref psock instance backing this \ref psock_br
 *                      instance.
 *
 * \note This \ref psock_br instance DOES NOT own the backing \ref psock
 * instance. The caller is responsible for releasing the resources for both when
 * they are no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p br must not reference a valid psock_br instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p sock must reference a valid \ref psock instance and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p br is set to a pointer to a valid \ref psock_br
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p br is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_br_create_from_psock)(
    RCPR_SYM(psock_br)** br, RCPR_SYM(allocator)* a, RCPR_SYM(psock)* sock);

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
 * \brief Read a SCM_RIGHTS message from the \ref psock instance, transferring
 * a copy of this open file descriptor from the peer to this process.
 *
 * \note This will only work for a Unix datagram socket, and this method will
 * verify the socket type.
 *
 * \param sock          Pointer to the \ref psock instance from which this
 *                      descriptor is read.
 * \param desc          Pointer to receive the descriptor on success.
 *
 * This method receives a duplicate an open descriptor from the peer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL. It must be a Unix domain datagram socket.
 *      - \p desc must be a valid pointer to an integer variable that will
 *        receive the descriptor.
 * \post
 *      - On success, \p desc is set to a descriptor that is owned by the caller
 *        and must be closed when no longer needed.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_descriptor)(
    RCPR_SYM(psock)* sock, int* desc);

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
 * \brief Write a SCM_RIGHTS message to the \ref psock instance, transferring
 * an open file descriptor to the peer.
 *
 * \note This will only work for a Unix datagram socket, and this method will
 * verify the socket type.
 *
 * \param sock          Pointer to the \ref psock instance over which this
 *                      descriptor is sent.
 * \param desc          The descriptor to transfer.
 *
 * This method sends a duplicate an open descriptor to the peer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL. It must be a Unix domain datagram socket.
 *      - \p desc must be a valid file descriptor that can be transferred to the
 *        peer socket.
 * \post
 *      - On success, a new descriptor is given to the peer that is a duplicate
 *        of \p desc.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_descriptor)(
    RCPR_SYM(psock)* sock, int desc);

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

/**
 * \brief For an output buffer backed psock, get a copy of the buffer. This
 * buffer belongs to the caller and must be reclaimed using the allocator passed
 * as a parameter.
 *
 * \param sock          Pointer to the \ref psock on which this operation
 *                      occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      buffer copy.
 * \param buffer        Pointer to the buffer pointer to be set with the copied
 *                      buffer on success.
 * \param buffer_size   Pointer to a variable to be set to the length of this
 *                      buffer on success.
 *
 * The \ref psock_from_buffer_get_output_buffer method creates a copy of the
 * current output buffer and returns it to the caller.  This copy is contiguous
 * in memory, whereas the output buffer written to by the psock may not be.
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
 *      - \p buffer must be a pointer to a valid pointer and must not be NULL.
 *      - \p buffer_size must be a pointer to a size_t value and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p buffer is set to a buffer containing a copy of the data
 *        written to this psock instance.
 *      - On success, \p buffer_size is set to the length of the buffer.
 *      - On failure, \p data is unchanged and an error status is returned.
 *      - On failure, \p data_size is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_from_buffer_get_output_buffer)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, void** buffer,
    size_t* buffer_size);

/**
 * \brief Read a line from the given buffered psock reader, using the supplied
 * buffer and size.
 *
 * \param buffer        Pointer to the buffer to receive the line on success.
 * \param size          Pointer to the size variable holding the buffer size and
 *                      updated with the number of bytes in the line on success.
 * \param br            Pointer to the \ref psock_br instance for this
 *                      operation.
 *
 * \note On success, \p buffer is updated with a line read from the
 * \ref psock_br instance pointed to by \p br. If the line is greater than the
 * buffer size, then ERROR_PSOCK_BR_READ_LINE_TRUNCATED is returned. In this
 * case, the buffer and size are both updated to the number of bytes read so
 * far, but the caller needs to call this function again and potentially
 * multiple times to finish reading the line.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock_br instance and must
 *        not be NULL.
 *      - \p buffer must be a pointer to a valid buffer that can hold at least
 *        \p size bytes and must not be NULL.
 *      - \p size must be a pointer to a size_t value and must not be NULL.
 *
 * \post
 *      - On success, \p size is updated with the number of bytes written to
 *        \p buffer, plus one, for the ASCII-Z null value.
 *      - If ERROR_PSOCK_BR_READ_LINE_TRUNCATED is returned, then \p size is
 *        updated to the maximum number of bytes written to \p buffer and the
 *        caller is responsible for making additional calls to this function to
 *        get the rest of the line. As with a successful return, the last byte
 *        written to \p buffer will be an ASCII-Z null value.
 *      - On failure, except for ERROR_PSOCK_BR_READ_LINE_TRUNCATED, \p buffer
 *        may be changed and an error status is returned.
 *      - On failure, except for ERROR_PSOCK_BR_READ_LINE_TRUNCATED, \p size is
 *        unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_br_read_line)(
    void* buffer, size_t* buffer_size, RCPR_SYM(psock_br)* br);

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

/**
 * \brief Given a \ref resource for a \ref psock instance, get the \ref psock
 * instance.
 *
 * \note that this MUST be a \ref psock \ref resource, or bad things can happen.
 * This cast should be model checked, and any function using this cast should
 * ensure that its contract specifies that the \ref resource is a \ref psock.
 *
 * \param r             The \ref resource to downcast to a \ref psock.
 *
 * \returns the \ref psock instance for this \ref resource.
 */
RCPR_SYM(psock)*
RCPR_SYM(psock_resource_handle_to_psock)(
    RCPR_SYM(resource)* r);

/**
 * \brief Given a \ref psock_br instance, return the resource handle for this
 * \ref psock_br instance.
 *
 * \param br            The \ref psock_br instance from which the resource
 *                      handle is returned.
 *
 * \returns the resource handle for this \ref psock_br instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(psock_br_resource_handle)(
    RCPR_SYM(psock_br)* br);

/**
 * \brief Given a \ref psock_br instance, returned the wrapped \ref psock
 * instance pointer that can be used to perform buffered reads using \ref psock
 * methods.
 *
 * \param br            The \ref psock_br instance from which the \ref psock
 *                      adapter instance is returned.
 *
 * \returns the \ref psock adapter instance for this \ref psock_br instance.
 */
RCPR_SYM(psock)*
RCPR_SYM(psock_br_psock_adapter)(
    RCPR_SYM(psock_br)* br);

/**
 * \brief Given a \ref psock instance, return the socket type for this
 * \ref psock instance, if applicable.
 *
 * \param sock          The \ref psock instance from which this socket type is
 *                      returned.
 * \returns the socket type for this \ref psock instance.
 */
RCPR_SYM(socket_type)
RCPR_SYM(psock_socket_type)(
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
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_psock_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(psock_read_fn) sym ## psock_read_fn; \
    typedef RCPR_SYM(psock_write_fn) sym ## psock_write_fn; \
    typedef RCPR_SYM(psock_accept_fn) sym ## psock_accept_fn; \
    typedef RCPR_SYM(psock_release_fn) sym ## psock_release_fn; \
    typedef RCPR_SYM(psock) sym ## psock; \
    typedef RCPR_SYM(psock_br) sym ## psock_br; \
    typedef RCPR_SYM(psock_boxed_type) sym ## psock_boxed_type; \
    typedef RCPR_SYM(socket_type) sym ## socket_type; \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_create_from_descriptor( \
        RCPR_SYM(psock)** x, RCPR_SYM(allocator)* y, int z) { \
            return RCPR_SYM(psock_create_from_descriptor)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_create_wrap_async( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        RCPR_SYM(fiber)* y, RCPR_SYM(psock)* z) { \
            return RCPR_SYM(psock_create_wrap_async)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_create_from_hostname_and_port( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const char* y, unsigned int z) { \
            return RCPR_SYM(psock_create_from_hostname_and_port)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_create_from_listen_address( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const struct sockaddr* y, socklen_t z) { \
            return RCPR_SYM(psock_create_from_listen_address)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_create_from_buffer( \
        RCPR_SYM(psock)** w, RCPR_SYM(allocator)* x, \
        const char* y, size_t z) { \
            return RCPR_SYM(psock_create_from_buffer)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_br_create_from_psock( \
        RCPR_SYM(psock_br)** x, RCPR_SYM(allocator)* y, RCPR_SYM(psock)* z) { \
            return RCPR_SYM(psock_br_create_from_psock)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_int64( \
        RCPR_SYM(psock)* x, int64_t* y) { \
            return RCPR_SYM(psock_read_boxed_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_uint64( \
        RCPR_SYM(psock)* x, uint64_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_int32( \
        RCPR_SYM(psock)* x, int32_t* y) { \
            return RCPR_SYM(psock_read_boxed_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_uint32( \
        RCPR_SYM(psock)* x, uint32_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_int16( \
        RCPR_SYM(psock)* x, int16_t* y) { \
            return RCPR_SYM(psock_read_boxed_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_uint16( \
        RCPR_SYM(psock)* x, uint16_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_int8( \
        RCPR_SYM(psock)* x, int8_t* y) { \
            return RCPR_SYM(psock_read_boxed_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_uint8( \
        RCPR_SYM(psock)* x, uint8_t* y) { \
            return RCPR_SYM(psock_read_boxed_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_bool( \
        RCPR_SYM(psock)* x, bool* y) { \
            return RCPR_SYM(psock_read_boxed_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_string( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, char** y, size_t* z) { \
            return RCPR_SYM(psock_read_boxed_string)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_boxed_data( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t* z) { \
            return RCPR_SYM(psock_read_boxed_data)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_int64( \
        RCPR_SYM(psock)* x, int64_t y) { \
            return RCPR_SYM(psock_write_boxed_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_uint64( \
        RCPR_SYM(psock)* x, uint64_t y) { \
            return RCPR_SYM(psock_write_boxed_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_int32( \
        RCPR_SYM(psock)* x, int32_t y) { \
            return RCPR_SYM(psock_write_boxed_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_uint32( \
        RCPR_SYM(psock)* x, uint32_t y) { \
            return RCPR_SYM(psock_write_boxed_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_int16( \
        RCPR_SYM(psock)* x, int16_t y) { \
            return RCPR_SYM(psock_write_boxed_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_uint16( \
        RCPR_SYM(psock)* x, uint16_t y) { \
            return RCPR_SYM(psock_write_boxed_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_int8( \
        RCPR_SYM(psock)* x, int8_t y) { \
            return RCPR_SYM(psock_write_boxed_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_uint8( \
        RCPR_SYM(psock)* x, uint8_t y) { \
            return RCPR_SYM(psock_write_boxed_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_bool( \
        RCPR_SYM(psock)* x, bool y) { \
            return RCPR_SYM(psock_write_boxed_bool)(x, y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_string( \
        RCPR_SYM(psock)* x, const char* y) { \
            return RCPR_SYM(psock_write_boxed_string)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_boxed_data( \
        RCPR_SYM(psock)* x, const void* y, size_t z) { \
            return RCPR_SYM(psock_write_boxed_data)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw( \
        RCPR_SYM(psock)* x, void* y, size_t* z) { \
            return RCPR_SYM(psock_read_raw)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_block( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_read_block)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_block( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_write_block)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_int64( \
        RCPR_SYM(psock)* x, int64_t* y) { \
            return RCPR_SYM(psock_read_raw_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_uint64( \
        RCPR_SYM(psock)* x, uint64_t* y) { \
            return RCPR_SYM(psock_read_raw_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_int32( \
        RCPR_SYM(psock)* x, int32_t* y) { \
            return RCPR_SYM(psock_read_raw_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_uint32( \
        RCPR_SYM(psock)* x, uint32_t* y) { \
            return RCPR_SYM(psock_read_raw_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_int16( \
        RCPR_SYM(psock)* x, int16_t* y) { \
            return RCPR_SYM(psock_read_raw_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_uint16( \
        RCPR_SYM(psock)* x, uint16_t* y) { \
            return RCPR_SYM(psock_read_raw_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_int8( \
        RCPR_SYM(psock)* x, int8_t* y) { \
            return RCPR_SYM(psock_read_raw_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_uint8( \
        RCPR_SYM(psock)* x, uint8_t* y) { \
            return RCPR_SYM(psock_read_raw_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_bool( \
        RCPR_SYM(psock)* x, bool* y) { \
            return RCPR_SYM(psock_read_raw_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_data( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t z) { \
            return RCPR_SYM(psock_read_raw_data)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_read_raw_descriptor( \
        RCPR_SYM(psock)* x, int* y) { \
            return RCPR_SYM(psock_read_raw_descriptor)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_int64( \
        RCPR_SYM(psock)* x, int64_t y) { \
            return RCPR_SYM(psock_write_raw_int64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_uint64( \
        RCPR_SYM(psock)* x, uint64_t y) { \
            return RCPR_SYM(psock_write_raw_uint64)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_int32( \
        RCPR_SYM(psock)* x, int32_t y) { \
            return RCPR_SYM(psock_write_raw_int32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_uint32( \
        RCPR_SYM(psock)* x, uint32_t y) { \
            return RCPR_SYM(psock_write_raw_uint32)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_int16( \
        RCPR_SYM(psock)* x, int16_t y) { \
            return RCPR_SYM(psock_write_raw_int16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_uint16( \
        RCPR_SYM(psock)* x, uint16_t y) { \
            return RCPR_SYM(psock_write_raw_uint16)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_int8( \
        RCPR_SYM(psock)* x, int8_t y) { \
            return RCPR_SYM(psock_write_raw_int8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_uint8( \
        RCPR_SYM(psock)* x, uint8_t y) { \
            return RCPR_SYM(psock_write_raw_uint8)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_bool( \
        RCPR_SYM(psock)* x, bool y) { \
            return RCPR_SYM(psock_write_raw_bool)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_data( \
        RCPR_SYM(psock)* x, const void* y, size_t z) { \
            return RCPR_SYM(psock_write_raw_data)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_write_raw_descriptor( \
        RCPR_SYM(psock)* x, int y) { \
            return RCPR_SYM(psock_write_raw_descriptor)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_accept( \
        RCPR_SYM(psock)* w, int* x, struct sockaddr* y, socklen_t* z) { \
            return RCPR_SYM(psock_accept)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_from_buffer_get_output_buffer( \
        RCPR_SYM(psock)* w, RCPR_SYM(allocator)* x, void** y, size_t* z) { \
            return RCPR_SYM(psock_from_buffer_get_output_buffer)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## psock_br_read_line( \
        void* x, size_t* y, RCPR_SYM(psock_br)* z) { \
            return RCPR_SYM(psock_br_read_line)(x,y,z); } \
    static inline RCPR_SYM(resource)* \
    sym ## psock_resource_handle( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_resource_handle)(x); } \
    static inline RCPR_SYM(psock)* \
    sym ## psock_resource_handle_to_psock( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(psock_resource_handle_to_psock)(x); } \
    static inline RCPR_SYM(resource)* \
    sym ## psock_br_resource_handle( \
        RCPR_SYM(psock_br)* x) { \
            return RCPR_SYM(psock_br_resource_handle)(x); } \
    static inline RCPR_SYM(psock)* \
    sym ## psock_br_psock_adapter( \
        RCPR_SYM(psock_br)* x) { \
            return RCPR_SYM(psock_br_psock_adapter)(x); } \
    static inline RCPR_SYM(socket_type) sym ## psock_socket_type( \
        RCPR_SYM(psock)* x) { \
            return RCPR_SYM(psock_socket_type)(x); } \
    static inline bool \
    sym ## prop_psock_valid( \
        const RCPR_SYM(psock)* x) { \
            return RCPR_SYM(prop_psock_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_psock_as(sym) \
    __INTERNAL_RCPR_IMPORT_psock_sym(sym ## _)
#define RCPR_IMPORT_psock \
    __INTERNAL_RCPR_IMPORT_psock_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
