/**
 * \file psock/psock_wrap_async_read.c
 *
 * \brief Read data from the given async \ref psock instance.
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

/**
 * \brief Read data from the given async \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Set to true if the read should block until all bytes are
 *                      read.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_wrap_async_read(psock* sock, void* data, size_t* size, bool block)
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

    /* loop through until all bytes are read. */
    size_t read_size = *size;
    *size = 0;
    uint8_t* dptr = (uint8_t*)data;
    while (read_size > 0)
    {
        size_t tmp_size = read_size;
        retval = s->wrapped->read_fn(s->wrapped, dptr, &tmp_size, block);
        if (ERROR_PSOCK_READ_WOULD_BLOCK == retval && block)
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
        /* if we shouldn't block until the read has completed, then return the
         * read size. */
        else if (ERROR_PSOCK_READ_WOULD_BLOCK && !block)
        {
            return retval;
        }
        /* if a different error occurred in the read, return it.*/
        else if (STATUS_SUCCESS != retval)
        {
            return retval;
        }
        /* if no data was read, then the peer closed the socket. */
        else if (0 == tmp_size)
        {
            return ERROR_PSOCK_READ_EOF;
        }

        /* update size and offset. */
        *size += tmp_size;
        read_size -= tmp_size;
        dptr += tmp_size;
    }

    return STATUS_SUCCESS;
}
