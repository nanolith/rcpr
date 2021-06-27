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

RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_uuid;

/**
 * \brief Accept a socket from a \ref psock listen socket instance.
 *
 * \param sock          The \ref psock instance to which to accept a socket.
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
status
RCPR_SYM(psock_wrap_async_accept)(
    RCPR_SYM(psock)* sock, int* idesc, struct sockaddr* addr,
    socklen_t* addrlen)
{
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != addr);
    RCPR_MODEL_ASSERT(NULL != addrlen);
    RCPR_MODEL_ASSERT(prop_valid_range(addr, *addrlen));
    RCPR_MODEL_ASSERT(PSOCK_TYPE_WRAP_ASYNC == sock->type);

    /* convert this to a async wrapped psock instance. */
    psock_wrap_async* s = (psock_wrap_async*)sock;
    RCPR_MODEL_ASSERT(prop_psock_valid(s->wrapped));

    /* get the underlying descriptor psock instance. */
    psock_from_descriptor* desc = (psock_from_descriptor*)s->wrapped;

    /* loop through until a socket has been accepted. */
    bool accepted = false;
    while (!accepted)
    {
        retval = s->wrapped->accept_fn(s->wrapped, idesc, addr, addrlen);
        if (ERROR_PSOCK_ACCEPT_WOULD_BLOCK == retval)
        {
            /* yield to the psock I/O discipline. */
            const rcpr_uuid* resume_id;
            int resume_event;
            void* resume_param;
            retval =
                fiber_discipline_yield(
                    s->psock_discipline,
                    FIBER_SCHEDULER_PSOCK_IO_YIELD_EVENT_WAIT_READ,
                    (void*)((ptrdiff_t)desc->descriptor),
                    &resume_id, &resume_event, &resume_param);
            if (STATUS_SUCCESS != retval)
            {
                return retval;
            }

            /* if the resume discipline doesn't match, maybe call the unexpected
             * handler. */
            if (
                memcmp(
                    resume_id, &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE,
                    sizeof(rcpr_uuid)))
            {
                /* if the unexpected handler is set, call it. */
                if (NULL != s->unexpected)
                {
                    retval =
                        s->unexpected(
                            &s->hdr, NULL, s->context, false,
                            resume_id, resume_event, resume_param);
                }
                /* otherwise, fail with an unexpected event error. */
                else
                {
                    retval = ERROR_PSOCK_UNEXPECTED_EVENT;
                }

                /* handle an error condition. */
                if (STATUS_SUCCESS != retval)
                {
                    return retval;
                }
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
