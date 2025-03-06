/**
 * \file psock/psock_wrap_async_recvmsg.c
 *
 * \brief Receive a message from the given async \ref psock instance.
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
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param ctx           User context (ignored).
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_recvmsg)(
    RCPR_SYM(psock)* sock, void* ctx, struct msghdr* msg, size_t* len,
    int flags)
{
    (void)ctx;
    status retval;
    const psock_vtable* wrapped_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != msg);
    RCPR_MODEL_ASSERT(NULL != len);
    RCPR_MODEL_ASSERT(prop_valid_range(data, *len));
    RCPR_MODEL_ASSERT(PSOCK_TYPE_WRAP_ASYNC == sock->type);

    /* convert this to a async wrapped psock instance. */
    psock_wrap_async* s = (psock_wrap_async*)sock;
    RCPR_MODEL_ASSERT(prop_sock_valid(s->wrapped));

    /* get the wrapped socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&wrapped_vtable,
            psock_resource_handle(s->wrapped));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify that recvmsg is set. */
    if (NULL == wrapped_vtable->recvmsg_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    /* loop until the receive succeeds. */
    for (;;)
    {
        retval =
            wrapped_vtable->recvmsg_fn(
                s->wrapped, s->wrapped->context, msg, len, flags);
        if (ERROR_PSOCK_READ_WOULD_BLOCK == retval)
        {
            /* yield to the psock I/O discipline. */
            retval = psock_read_block(sock);
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
}

#endif /* RCPR_FIBER_FOUND */
