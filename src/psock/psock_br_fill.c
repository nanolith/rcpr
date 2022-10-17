/**
 * \file psock/psock_br_fill.c
 *
 * \brief Attempt to fill a buffered psock buffer.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Fill the \ref psock_br buffer with as much data as the backing \ref
 * psock can provide in a non-blocking read.
 *
 * \param br            The \ref psock_br instance to fill.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_br_fill)(
    RCPR_SYM(psock_br)* br)
{
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(br));

    /* if the offset is not zero, then shift the data down in the buffer. */
    if (br->offset > 0)
    {
        /* shift the data down. */
        memmove(
            br->buffer, br->buffer + br->offset, br->current_size - br->offset);

        /* fix up current size. */
        br->current_size -= br->offset;

        /* fix up offset. */
        br->offset = 0;
    }

    /* read as many bytes as we can from the wrapped socket. */
    size_t read_bytes = br->max_size - br->current_size;
    retval =
        br->wrapped->read_fn(
            br->wrapped, br->buffer + br->current_size, &read_bytes, false);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* if zero bytes were read, then the socket is closed. */
    if (0 == read_bytes)
    {
        return ERROR_PSOCK_READ_GENERAL;
    }

    /* adjust the current size accordingly. */
    br->current_size += read_bytes;

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}
