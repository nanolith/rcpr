/**
 * \file psock/psock_create_from_descriptor.c
 *
 * \brief Create a \ref psock instance from a descriptor.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);
static RCPR_SYM(socket_type) psock_get_socket_type_from_descriptor(int desc);

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/* the vtable entry for the psock from descriptor instance. */
RCPR_VTABLE
psock_vtable psock_from_descriptor_vtable = {
    .hdr = { &psock_from_descriptor_release },
    .read_fn = &psock_from_descriptor_read,
    .write_fn = &psock_from_descriptor_write,
    .accept_fn = &psock_from_descriptor_accept,
    .sendmsg_fn = NULL,
    .recvmsg_fn = NULL,
};

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
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a, int descriptor)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != sock);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(descriptor >= 0);

    /* attempt to allocate memory for this descriptor psock. */
    psock_from_descriptor* ps = NULL;
    int retval =
        allocator_allocate(a, (void**)&ps, sizeof(psock_from_descriptor));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear out the structure. */
    memset(ps, 0, sizeof(psock_from_descriptor));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the release method. */
    resource_init(&ps->hdr.hdr, &psock_from_descriptor_vtable.hdr);

    /* set the descriptor. */
    ps->descriptor = descriptor;

    /* set the type. */
    ps->hdr.type = PSOCK_TYPE_DESCRIPTOR;

    /* set the socket type. */
    ps->hdr.socktype = psock_get_socket_type_from_descriptor(descriptor);

    /* set the allocator. */
    ps->hdr.alloc = a;

    /* set the callbacks. */
    ps->hdr.sendmsg_fn = &psock_from_descriptor_sendmsg;
    ps->hdr.recvmsg_fn = &psock_from_descriptor_recvmsg;

    /* set the socket. */
    *sock = &ps->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_psock_valid(*sock));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Get the socket type from the given descriptor.
 *
 * \param desc      The descriptor to query.
 *
 * \returns an applicable socket type.
 */
static RCPR_SYM(socket_type) psock_get_socket_type_from_descriptor(int desc)
{
    int type;
    socklen_t length = sizeof(type);

    if (getsockopt(desc, SOL_SOCKET, SO_TYPE, &type, &length) < 0)
    {
        return PSOCK_SOCKET_TYPE_OTHER;
    }
    else if (SOCK_STREAM == type)
    {
        return PSOCK_SOCKET_TYPE_STREAM;
    }
    else if (SOCK_DGRAM == type)
    {
        return PSOCK_SOCKET_TYPE_DATAGRAM;
    }
    else
    {
        return PSOCK_SOCKET_TYPE_OTHER;
    }
}
