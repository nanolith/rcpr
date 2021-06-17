/**
 * \file psock/psock_wrap_async_write.c
 *
 * \brief Write data to the given async \ref psock instance.
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

/**
 * \brief Write data to the given async \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status
RCPR_SYM(psock_wrap_async_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size)
{
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(NULL != data);
    MODEL_ASSERT(NULL != size);
    MODEL_ASSERT(prop_valid_range(data, *size));
    MODEL_ASSERT(PSOCK_TYPE_WRAP_ASYNC == sock->type);

    /* convert this to a async wrapped psock instance. */
    psock_wrap_async* s = (psock_wrap_async*)sock;
    MODEL_ASSERT(prop_psock_valid(s->wrapped));

    /* get the underlying descriptor psock instance. */
    psock_from_descriptor* desc = (psock_from_descriptor*)s->wrapped;

    /* loop through until all bytes are written. */
    size_t write_size = *size;
    const uint8_t* dptr = (uint8_t*)data;
    while (write_size > 0)
    {
        size_t tmp_size = write_size;
        retval = s->wrapped->write_fn(s->wrapped, dptr, &tmp_size);
        if (ERROR_PSOCK_WRITE_WOULD_BLOCK == retval)
        {
            /* reset tmp_size. */
            tmp_size = 0;

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
                /* if the unexpected handler is set, call it. */
                if (NULL != s->unexpected)
                {
                    retval =
                        s->unexpected(
                            &s->hdr, NULL, s->context, true,
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
        /* if a different error occurred in the write, return it.*/
        else if (STATUS_SUCCESS != retval)
        {
            *size -= write_size;
            return retval;
        }
        /* if no data was written, then the peer closed the socket. */
        else if (0 == tmp_size)
        {
            return ERROR_PSOCK_WRITE_EOF;
        }

        /* update size and offset. */
        write_size -= tmp_size;
        dptr += tmp_size;
    }

    return STATUS_SUCCESS;

}
