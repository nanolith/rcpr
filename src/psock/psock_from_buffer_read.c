/**
 * \file psock/psock_from_buffer_read.c
 *
 * \brief Read data from a buffer.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Ignored for raw buffer reads.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_buffer_read)(
    RCPR_SYM(psock)* sock, void* data, size_t* size, bool block)
{
    /* the block flag is meaningless here. */
    (void)block;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != size);
    RCPR_MODEL_ASSERT(prop_valid_range(data, *size));

    /* cast to the derived type. */
    psock_from_buffer* pb = (psock_from_buffer*)sock;

    /* if we are at EOF, return EOF. */
    if (NULL == pb->input_buffer
     || pb->buffer_read_offset >= pb->input_buffer_size)
    {
        return ERROR_PSOCK_READ_EOF;
    }

    /* compute the moximum number of bytes we can read. */
    size_t max_size = pb->input_buffer_size - pb->buffer_read_offset;
    if (*size > max_size)
    {
        *size = max_size;
    }

    /* "read" the bytes. */
    memcpy(data, pb->input_buffer + pb->buffer_read_offset, *size);

    /* update counters. */
    pb->buffer_read_offset += *size;

    return STATUS_SUCCESS;
}
