/**
 * \file psock/psock_create_from_buffer.c
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

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

/* the vtable entry for the psock from buffer instance. */
RCPR_VTABLE
psock_vtable psock_from_buffer_vtable = {
    .hdr = { &psock_from_buffer_release },
    .read_fn = &psock_from_buffer_read,
    .write_fn = &psock_from_buffer_write,
    .accept_fn = &psock_from_buffer_accept,
    .sendmsg_fn = NULL,
    .recvmsg_fn = NULL,
};

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
    const char* buffer, size_t size)
{
    int retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != sock);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT((buffer != NULL) || (buffer == NULL && size == 0));

    /* attempt to allocate memory for this buffer psock. */
    psock_from_buffer* ps = NULL;
    retval = allocator_allocate(a, (void**)&ps, sizeof(psock_from_buffer));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out the structure. */
    memset(ps, 0, sizeof(psock_from_buffer));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the release method. */
    resource_init(&ps->hdr.hdr, &psock_from_buffer_vtable.hdr);

    /* set the type. */
    ps->hdr.type = PSOCK_TYPE_BUFFER;

    /* set the socket type. */
    ps->hdr.socktype = PSOCK_SOCKET_TYPE_OTHER;

    /* set the allocator. */
    ps->hdr.alloc = a;

    /* is this a read buffer? */
    if (buffer != NULL)
    {
        /* set the input buffer size. */
        ps->input_buffer_size = size;

        /* create the input buffer. */
        retval =
            allocator_allocate(
                ps->hdr.alloc, (void**)&ps->input_buffer,
                ps->input_buffer_size);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_psock;
        }

        /* copy the contents of the input buffer. */
        memcpy(ps->input_buffer, buffer, ps->input_buffer_size);
    }
    else
    {
        /* create the queue for holding the output buffer. */
        retval = slist_create(&ps->output_queue, ps->hdr.alloc);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_psock;
        }

        /* create the initial output buffer. */
        retval =
            allocator_allocate(
                ps->hdr.alloc, (void**)&ps->output_curr_buffer,
                PSOCK_BUFFER_SIZE);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_psock;
        }

        /* set the output buffer size. */
        ps->output_buffer_size = PSOCK_BUFFER_SIZE;
    }

    /* set the socket. */
    *sock = &ps->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_psock_valid(*sock));
    
    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_psock:
    release_retval = resource_release(&ps->hdr.hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}
