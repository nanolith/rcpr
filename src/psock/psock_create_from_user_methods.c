/**
 * \file psock/psock_create_from_user_methods.c
 *
 * \brief Create a \ref psock instance user methods and user data.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);
static status psock_from_user_methods_release(RCPR_SYM(resource)* r);
static status psock_from_user_methods_read(
    psock* sock, void* ctx, void* data, size_t* size, bool block);
static status psock_from_user_methods_write(
    psock* sock, void* ctx, const void* data, size_t* size);
static status psock_from_user_methods_accept(
    psock* sock, void* ctx, int* desc, struct sockaddr* addr,
    socklen_t* addrlen);
static status psock_from_user_methods_sendmsg(
    psock* sock, void* ctx, const struct msghdr* msg, int flags);
static status psock_from_user_methods_recvmsg(
    psock* sock, void* ctx, struct msghdr* msg, size_t* len, int flags);

/* the vtable entry for the psock from user methods instance. */
RCPR_VTABLE
psock_vtable psock_from_user_methods_vtable = {
    .hdr = { &psock_from_user_methods_release },
    .read_fn = &psock_from_user_methods_read,
    .write_fn = &psock_from_user_methods_write,
    .accept_fn = &psock_from_user_methods_accept,
    .sendmsg_fn = &psock_from_user_methods_sendmsg,
    .recvmsg_fn = &psock_from_user_methods_recvmsg,
    .release_fn = NULL,
};

/**
 * \brief Create a custom \ref psock instance backed by user-supplied methods.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param context       The context pointer to use for this instance.
 * \param vtable        The vtable to use for this instance.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the descriptor, which will be closed when this resource is
 * released.
 *
 * The \ref psock instance created is backed by user-specific methods and
 * context. This instance does not own the context, and it is up to the user to
 * ensure that it is cleaned up as appropriate.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p context is a user-defined value and can be NULL.
 *      - \p vtable must be valid; the accept, recvmsg, and sendmsg functions
 *        are optional, but all other functions must be defined. This vtable
 *        must be defined as an RCPR_VTABLE so it is linked in the right
 *        segment.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_from_user_methods)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a,
    void* context, const RCPR_SYM(psock_vtable)* vtable)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != sock);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(NULL != vtable);

    /* attempt to allocate memory for this user psock. */
    psock_from_user_methods* ps = NULL;
    int retval = allocator_allocate(a, (void**)&ps, sizeof(*ps));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear out the structure. */
    memset(ps, 0, sizeof(*ps));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the release method. */
    resource_init(&ps->hdr.hdr, &psock_from_user_methods_vtable.hdr);

    /* set the context. */
    ps->hdr.context = context;

    /* set the user vtable. */
    ps->user_vtable = vtable;

    /* set the type. */
    ps->hdr.type = PSOCK_TYPE_USER;

    /* set the socket type. */
    ps->hdr.socktype = PSOCK_SOCKET_TYPE_OTHER;

    /* set the allocator. */
    ps->hdr.alloc = a;

    /* set the socket. */
    *sock = &ps->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_psock_valid(*sock));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Release a psock_from_user_methods resource.
 *
 * \param r             Pointer to the psock_from_user_methods resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
static status psock_from_user_methods_release(RCPR_SYM(resource)* r)
{
    status retval = STATUS_SUCCESS, release_retval;
    psock_from_user_methods* ps = (psock_from_user_methods*)r;

    /* cache allocator. */
    allocator* alloc = ps->hdr.alloc;

    /* cache user vtable. */
    const psock_vtable* vtable = ps->user_vtable;

    /* call release method if set. */
    if (NULL != vtable->release_fn)
    {
        release_retval = vtable->release_fn(&ps->hdr, ps->hdr.context);
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

    /* clear memory. */
    memset(ps, 0, sizeof(*ps));

    /* reclaim memory. */
    release_retval = allocator_reclaim(alloc, ps);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    /* return decoded status. */
    return retval;
}

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param ctx           User context.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Should we block until the read is complete?
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
static status psock_from_user_methods_read(
    psock* sock, void* ctx, void* data, size_t* size, bool block)
{
    (void)ctx;
    psock_from_user_methods* ps = (psock_from_user_methods*)sock;

    return ps->user_vtable->read_fn(sock, ps->hdr.context, data, size, block);
}

/**
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param ctx           User context.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
static status psock_from_user_methods_write(
    psock* sock, void* ctx, const void* data, size_t* size)
{
    (void)ctx;
    psock_from_user_methods* ps = (psock_from_user_methods*)sock;

    return ps->user_vtable->write_fn(sock, ps->hdr.context, data, size);
}

/**
 * \brief Accept a socket from a \ref psock listen socket instance.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param ctx           User context (ignored).
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
static status psock_from_user_methods_accept(
    psock* sock, void* ctx, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    (void)ctx;
    psock_from_user_methods* ps = (psock_from_user_methods*)sock;

    /* does this user method exist? */
    if (NULL == ps->user_vtable->accept_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    return
        ps->user_vtable->accept_fn(sock, ps->hdr.context, desc, addr, addrlen);
}

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param ctx           User context.
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
static status psock_from_user_methods_sendmsg(
    psock* sock, void* ctx, const struct msghdr* msg, int flags)
{
    (void)ctx;
    psock_from_user_methods* ps = (psock_from_user_methods*)sock;

    /* does this user method exist? */
    if (NULL == ps->user_vtable->sendmsg_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    return ps->user_vtable->sendmsg_fn(sock, ps->hdr.context, msg, flags);
}

/**
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param ctx           User context.
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
static status psock_from_user_methods_recvmsg(
    psock* sock, void* ctx, struct msghdr* msg, size_t* len, int flags)
{
    (void)ctx;
    psock_from_user_methods* ps = (psock_from_user_methods*)sock;

    /* does this user method exist? */
    if (NULL == ps->user_vtable->recvmsg_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    return ps->user_vtable->recvmsg_fn(sock, ps->hdr.context, msg, len, flags);
}
