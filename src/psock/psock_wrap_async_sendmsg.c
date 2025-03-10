/**
 * \file psock/psock_wrap_async_sendmsg.c
 *
 * \brief Send a message over the given async \ref psock instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <unistd.h>

#include "psock_internal.h"

#ifdef RCPR_FIBER_FOUND

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param ctx           User context (ignored).
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_sendmsg)(
    RCPR_SYM(psock)* sock, void* ctx, const struct msghdr* msg, int flags)
{
    (void)ctx;
    status retval;
    const psock_vtable* wrapped_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != msg);
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

    /* verify that sendmsg is defined. */
    if (NULL == wrapped_vtable->sendmsg_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    /* loop through until the message is sent. */
    for (;;)
    {
        retval =
            wrapped_vtable->sendmsg_fn(
                s->wrapped, s->wrapped->context, msg, flags);
        if (ERROR_PSOCK_WRITE_WOULD_BLOCK == retval)
        {
            /* yield to the psock I/O discipline. */
            retval = psock_write_block(sock);
            if (STATUS_SUCCESS != retval)
            {
                return retval;
            }
        }
        /* otherwise, return the status code received. */
        else
        {
            return retval;
        }
    }

    /* success. */
    return STATUS_SUCCESS;
}

#endif /* RCPR_FIBER_FOUND */
