/**
 * \file psock/psock_write_block.c
 *
 * \brief Block until a write is available.
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
 * \brief Block until the socket is available for writing.
 *
 * \param sock          Pointer to the \ref psock pointer on which to block.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE if this \ref psock instance is not a
 *        non-blocking instance.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *
 * \post
 *      - On success, this \ref psock instance is available for write, or
 *        the peer has closed this \ref psock instance, or a connection error on
 *        this \ref psock instance has occurred.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_block)(RCPR_SYM(psock)* sock)
{
    status retval;
    bool done = false;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(PSOCK_TYPE_WRAP_ASYNC == sock->type);

    /* this has to be an async psock instance. */
    if (PSOCK_TYPE_WRAP_ASYNC != sock->type)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* convert this to a async wrapped psock instance. */
    psock_wrap_async* s = (psock_wrap_async*)sock;
    RCPR_MODEL_ASSERT(prop_psock_valid(s->wrapped));

    /* get the underlying descriptor psock instance. */
    psock_from_descriptor* desc = (psock_from_descriptor*)s->wrapped;

    while (!done)
    {
        /* yield to the psock I/O discipline. */
        const rcpr_uuid* resume_id;
        int resume_event;
        void* resume_param;
        retval =
            fiber_discipline_yield(
                s->psock_discipline,
                FIBER_SCHEDULER_PSOCK_IO_YIELD_EVENT_WAIT_WRITE,
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
            /* try to call the unexpected event handler. */
            retval =
                fiber_unexpected_event(
                    s->fib, resume_id, resume_event, resume_param,
                    &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE,
                    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_WRITE);
            if (STATUS_SUCCESS != retval)
            {
                return retval;
            }
        }
        else
        {
            done = true;
        }
    }

    return STATUS_SUCCESS;
}
