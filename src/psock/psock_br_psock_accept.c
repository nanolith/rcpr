/**
 * \file psock/psock_br_psock_accept.c
 *
 * \brief Accept a socket from a listen descriptor.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

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
status RCPR_SYM(psock_br_psock_accept)(
    RCPR_SYM(psock)* sock, void* ctx, int* desc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    (void)ctx;
    status retval;
    const psock_vtable* wrapped_vtable;
    psock_br* br = (psock_br*)sock;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(br));

    /* get the wrapped socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&wrapped_vtable,
            psock_resource_handle(br->wrapped));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify that the accept function is set. */
    if (NULL == wrapped_vtable->accept_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    /* pass through to the wrapped socket. */
    return
        wrapped_vtable->accept_fn(
            br->wrapped, br->wrapped->context, desc, addr, addrlen);
}
