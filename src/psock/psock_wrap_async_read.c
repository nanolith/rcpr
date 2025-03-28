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

#ifdef RCPR_FIBER_FOUND

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Read data from the given async \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param ctx           User context (ignored).
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Set to true if the read should block until all bytes are
 *                      read.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_wrap_async_read)(
    RCPR_SYM(psock)* sock, void* ctx, void* data, size_t* size, bool block)
{
    (void)ctx;
    status retval;
    const psock_vtable* wrapped_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != size);
    RCPR_MODEL_ASSERT(prop_valid_range(data, *size));
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

    /* loop through until all bytes are read. */
    size_t read_size = *size;
    *size = 0;
    uint8_t* dptr = (uint8_t*)data;
    while (read_size > 0)
    {
        size_t tmp_size = read_size;
        retval =
            wrapped_vtable->read_fn(
                s->wrapped, s->wrapped->context, dptr, &tmp_size, block);
        if (ERROR_PSOCK_READ_WOULD_BLOCK == retval && block)
        {
            /* yield to the psock I/O discipline. */
            retval = psock_read_block(sock);
            if (STATUS_SUCCESS != retval)
            {
                return retval;
            }
            continue;
        }
        /* if we shouldn't block until the read has completed, then return. */
        else if (ERROR_PSOCK_READ_WOULD_BLOCK == retval && !block)
        {
            if (*size > 0)
            {
                return STATUS_SUCCESS;
            }
            else
            {
                return retval;
            }
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

#endif /* RCPR_FIBER_FOUND */
