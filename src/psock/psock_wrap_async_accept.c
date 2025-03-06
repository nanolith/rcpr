/**
 * \file psock/psock_wrap_async_accept.c
 *
 * \brief Accept data from the given async listen \ref psock instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

#ifdef RCPR_FIBER_FOUND

RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

/**
 * \brief Accept a socket from a \ref psock listen socket instance.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
 * \param ctx           User context (ignored).
 * \param idesc         Pointer to the integer field to hold the accepted
 *                      descriptor.
 * \param addr          The address of the accepted socket.
 * \param addrlen       On input, the max size of the address field; on output,
 *                      the size of the address field.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_accept)(
    RCPR_SYM(psock)* sock, void* ctx, int* idesc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    (void)ctx;
    status retval;
    const psock_vtable* wrapped_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != addr);
    RCPR_MODEL_ASSERT(NULL != addrlen);
    RCPR_MODEL_ASSERT(prop_valid_range(addr, *addrlen));
    RCPR_MODEL_ASSERT(PSOCK_TYPE_WRAP_ASYNC == sock->type);

    /* convert this to a async wrapped psock instance. */
    psock_wrap_async* s = (psock_wrap_async*)sock;
    RCPR_MODEL_ASSERT(prop_psock_valid(s->wrapped));

    /* get the wrapped socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&wrapped_vtable,
            psock_resource_handle(s->wrapped));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify that the accept function is set. */
    if (NULL == wrapped_vtable->accept_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    /* loop through until a socket has been accepted. */
    bool accepted = false;
    while (!accepted)
    {
        retval =
            wrapped_vtable->accept_fn(
                s->wrapped, s->wrapped->context, idesc, addr, addrlen);
        if (ERROR_PSOCK_ACCEPT_WOULD_BLOCK == retval)
        {
            /* yield to the psock I/O discipline. */
            retval = psock_read_block(sock);
            if (STATUS_SUCCESS != retval)
            {
                return retval;
            }
        }
        /* if a different error occurred in the accept, return it.*/
        else if (STATUS_SUCCESS != retval)
        {
            return retval;
        }
        /* otherwise, a valid descriptor was accepted. */
        else
        {
            accepted = true;
        }
    }

    return STATUS_SUCCESS;
}

#endif /* RCPR_FIBER_FOUND */
