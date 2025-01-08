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

/**
 * \brief Send a message over the \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to send a message.
 * \param msg           Pointer to the message to send.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_sendmsg)(
    RCPR_SYM(psock)* sock, const struct msghdr* msg, int flags)
{
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != msg);
    RCPR_MODEL_ASSERT(PSOCK_TYPE_WRAP_ASYNC == sock->type);

    /* convert this to a async wrapped psock instance. */
    psock_wrap_async* s = (psock_wrap_async*)sock;
    RCPR_MODEL_ASSERT(prop_psock_valid(s->wrapped));

    /* loop through until the message is sent. */
    for (;;)
    {
        retval = s->wrapped->sendmsg_fn(s->wrapped, msg, flags);
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
