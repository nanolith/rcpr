/**
 * \file psock/psock_create_from_descriptor.c
 *
 * \brief Create a \ref psock instance from a descriptor.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

/* forward decls. */
static status psock_from_descriptor_release(resource*);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);

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
    psock** sock, allocator* a, int descriptor)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != sock);
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(descriptor >= 0);

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
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ps->hdr.MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(ps->hdr.MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the release method. */
    resource_init(&ps->hdr.hdr, &psock_from_descriptor_release);

    /* set the descriptor. */
    ps->descriptor = descriptor;

    /* set the type. */
    ps->hdr.type = PSOCK_TYPE_DESCRIPTOR;

    /* set the allocator. */
    ps->hdr.alloc = a;

    /* set the callbacks. */
    ps->hdr.read_fn = &psock_from_descriptor_read;
    ps->hdr.write_fn = &psock_from_descriptor_write;
    ps->hdr.accept_fn = &psock_from_descriptor_accept;

    /* set the socket. */
    *sock = &ps->hdr;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_psock_valid(*sock));

    /* success. */
    return STATUS_SUCCESS;
}

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
static status psock_from_descriptor_release(resource* r)
{
    psock_from_descriptor* ps = (psock_from_descriptor*)r;

    /* close the descriptor. */
    close(ps->descriptor);

    /* clean up. */
    allocator* a = ps->hdr.alloc;
    memset(ps, 0, sizeof(psock_from_descriptor));

    /* if reclaiming this psock instance succeeds, so does this release. */
    return
        allocator_reclaim(a, ps);
}
