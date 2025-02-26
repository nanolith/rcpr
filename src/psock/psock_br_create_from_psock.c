/**
 * \file psock/psock_br_create_from_psock.c
 *
 * \brief Create a \ref psock_br instance backed by the given \ref psock
 * instance.
 *
 * \copyright 2022-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/vtable.h>
#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock_br);

/* the vtable entry for the psock br instance. */
RCPR_VTABLE
psock_vtable psock_br_vtable = {
    .hdr = { &psock_br_release },
    .read_fn = &psock_br_psock_read,
    .write_fn = &psock_br_psock_write,
};

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
    RCPR_SYM(psock_br)** br, RCPR_SYM(allocator)* a, RCPR_SYM(psock)* sock)
{
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != br);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));

    /* attempt to allocate memory for this buffered psock. */
    psock_br* tmp = NULL;
    retval = allocator_allocate(a, (void**)&tmp, sizeof(psock_br));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out the structure. */
    memset(tmp, 0, sizeof(*tmp));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(psock_br), psock_br);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock_br), psock_br);

    /* set the release method. */
    resource_init(&tmp->hdr.hdr, &psock_br_vtable.hdr);

    /* set the allocator. */
    tmp->hdr.alloc = a;

    /* set the type. */
    tmp->hdr.type = PSOCK_TYPE_BUFFERED;

    /* set the socket. */
    tmp->wrapped = sock;

    /* set the callbacks. */
    tmp->hdr.accept_fn = &psock_br_psock_accept;
    tmp->hdr.sendmsg_fn = &psock_br_psock_sendmsg;
    tmp->hdr.recvmsg_fn = &psock_br_psock_recvmsg;

    /* set the maximum buffer size. */
    tmp->max_size = PSOCK_BR_BUFFER_SIZE;

    /* attempt to allocate the buffer. */
    retval = allocator_allocate(a, (void**)&tmp->buffer, tmp->max_size);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_tmp;
    }

    /* set the result pointer on success. */
    *br = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(*br));

    goto done;

cleanup_tmp:
    release_retval = resource_release(&tmp->hdr.hdr);
    if (STATUS_SUCCESS != retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}
