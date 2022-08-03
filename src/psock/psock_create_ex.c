/**
 * \file psock/psock_create_from_descriptor.c
 *
 * \brief Create a \ref psock instance from a descriptor.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/psock.h>
#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);

/**
 * \brief Create a user \ref psock instance.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      psock resource.
 * \param ctx           The user context pointer for this custom psock instance.
 * \param read_fn       Pointer to the user read function for this socket or
 *                      NULL if not defined.
 * \param write_fn      Pointer to the user write function for this socket or
 *                      NULL if not defined.
 * \param accept_fn     Pointer to the user accept function for this socket or
 *                      NULL if not defined.
 * \param release_fn    Pointer to the user release function, which is called
 *                      when this \ref psock resource is released.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the descriptor, which will be closed when this resource is
 * released.
 *
 * The \p release_fn will be called when this resource is released. This
 * function is NOT responsible for releasing this \ref psock resource and is
 * only provided so that any user data (e.g. the context structure) can be
 * released when this \ref psock instance is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sock must not reference a valid sock instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - All other parameters are optional. If not defined, then calling the
 *        top-level functions that map to these user functions will result in a
 *        failure.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_create_ex)(
    RCPR_SYM(psock)** sock, RCPR_SYM(allocator)* a, void* ctx,
    RCPR_SYM(psock_read_fn) read_fn, RCPR_SYM(psock_write_fn) write_fn,
    RCPR_SYM(psock_accept_fn) accept_fn, RCPR_SYM(psock_release_fn) release_fn)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != sock);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));

    /* attempt to allocate memory for this user psock. */
    psock_ex* ps = NULL;
    int retval =
        allocator_allocate(a, (void**)&ps, sizeof(psock_ex));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear out the structure. */
    memset(ps, 0, sizeof(psock_ex));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(ps->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the release method. */
    resource_init(&ps->hdr.hdr, &psock_ex_release);

    /* set the context. */
    ps->ctx = ctx;

    /* set the user functions. */
    ps->ex_read_fn = read_fn;
    ps->ex_write_fn = write_fn;
    ps->ex_accept_fn = accept_fn;
    ps->ex_release_fn = release_fn;

    /* set the type. */
    ps->hdr.type = PSOCK_TYPE_USER;

    /* set the socket type. */
    ps->hdr.socktype = PSOCK_SOCKET_TYPE_OTHER;

    /* set the allocator. */
    ps->hdr.alloc = a;

    /* set the callbacks. */
    ps->hdr.read_fn = &psock_ex_read;
    ps->hdr.write_fn = &psock_ex_write;
    ps->hdr.accept_fn = &psock_ex_accept;

    /* set the socket. */
    *sock = &ps->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_psock_valid(*sock));

    /* success. */
    return STATUS_SUCCESS;
}
