/**
 * \file psock/psock_br_psock_read.c
 *
 * \brief Read data from a psock.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Read data from the given \ref psock instance.
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
status RCPR_SYM(psock_br_psock_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block)
{
    status retval;

    /* get the buffered reader. */
    psock_br* br = (psock_br*)sock;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(br));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != *size);

    /* compute the number of available bytes in the buffer. */
    size_t available_bytes = br->current_size - br->offset;
    size_t read_bytes = 0;
    size_t requested_bytes = *size;
    uint8_t* bdata = (uint8_t*)data;

    do {
        /* attempt to fill the buffer if we don't have enough bytes. */
        if (available_bytes < requested_bytes)
        {
            retval = psock_br_fill(br);
            if (STATUS_SUCCESS != retval)
            {
                /* update size with the number of read bytes. */
                *size = read_bytes;

                goto done;
            }
        }

        /* re-compute the number of available bytes in the buffer. */
        available_bytes = br->current_size - br->offset;

        /* compute the number of bytes to copy. */
        size_t copy_bytes =
            available_bytes < requested_bytes
                ?  available_bytes
                : requested_bytes;

        /* copy bytes from the buffer. */
        memcpy(bdata, br->buffer + br->offset, copy_bytes);

        /* adjust offset. */
        br->offset += copy_bytes;

        /* adjust available bytes. */
        available_bytes -= copy_bytes;

        /* adjust requested bytes. */
        requested_bytes -= copy_bytes;

        /* adjust read bytes. */
        read_bytes += copy_bytes;

        /* adjust the data pointer. */
        bdata += copy_bytes;
        
    } while (block && requested_bytes > 0);

    /* update size with the number of read bytes. */
    *size = read_bytes;

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}
