/**
 * \file psock/psock_br_read_line.c
 *
 * \brief Read a line from a buffered psock reader.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

RCPR_IMPORT_psock_internal;

/**
 * \brief Read a line from the given buffered psock reader, using the supplied
 * buffer and size.
 *
 * \param buffer        Pointer to the buffer to receive the line on success.
 * \param size          Pointer to the size variable holding the buffer size and
 *                      updated with the number of bytes in the line on success.
 * \param br            Pointer to the \ref psock_br instance for this
 *                      operation.
 *
 * \note On success, \p buffer is updated with a line read from the
 * \ref psock_br instance pointed to by \p br. If the line is greater than the
 * buffer size, then ERROR_PSOCK_BR_READ_LINE_TRUNCATED is returned. In this
 * case, the buffer and size are both updated to the number of bytes read so
 * far, but the caller needs to call this function again and potentially
 * multiple times to finish reading the line.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock_br instance and must
 *        not be NULL.
 *      - \p buffer must be a pointer to a valid buffer that can hold at least
 *        \p size bytes and must not be NULL.
 *      - \p size must be a pointer to a size_t value and must not be NULL.
 *
 * \post
 *      - On success, \p size is updated with the number of bytes written to
 *        \p buffer, plus one, for the ASCII-Z null value.
 *      - If ERROR_PSOCK_BR_READ_LINE_TRUNCATED is returned, then \p size is
 *        updated to the maximum number of bytes written to \p buffer and the
 *        caller is responsible for making additional calls to this function to
 *        get the rest of the line. As with a successful return, the last byte
 *        written to \p buffer will be an ASCII-Z null value.
 *      - On failure, except for ERROR_PSOCK_BR_READ_LINE_TRUNCATED, \p buffer
 *        may be changed and an error status is returned.
 *      - On failure, except for ERROR_PSOCK_BR_READ_LINE_TRUNCATED, \p size is
 *        unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_br_read_line)(
    void* buffer, size_t* buffer_size, RCPR_SYM(psock_br)* br)
{
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(br));
    RCPR_MODEL_ASSERT(buffer != NULL);
    RCPR_MODEL_ASSERT(buffer_size != NULL);
    RCPR_MODEL_ASSERT(*buffer_size > 1);

    /* the buffer size must be greater than one. */
    if (*buffer_size <= 1)
    {
        retval = ERROR_PSOCK_BR_READ_LINE_BUFFER_SIZE_TOO_SMALL;
        goto done;
    }

    /* compute available bytes. */
    size_t available_input = br->current_size - br->offset;
    size_t buffer_remaining = *buffer_size - 1;

    /* set copied byte counter. */
    size_t committed_bytes = 0;
    size_t copied_bytes = 0;

    /* make buffer easier to work with. */
    uint8_t* bbuf = (uint8_t*)buffer;

    /* temporary pointer for the input. */
    const uint8_t* inp = br->buffer + br->offset;

    /* outer loop. */
    while (buffer_remaining > 0)
    {
        /* while there's buffer space, data to copy, and not EOL, copy data. */
        while (buffer_remaining > 0 && available_input > 0 && '\n' != *inp)
        {
            *bbuf = *inp;
            ++bbuf; ++inp;
            ++copied_bytes;
            --available_input;
            --buffer_remaining;
        }

        /* base case: we've entered EOL. */
        if (available_input > 0 && '\n' == *inp)
        {
            /* adjust the offset, consuming the newline. */
            br->offset += copied_bytes + 1;

            /* fix up the output buffer. */
            *bbuf = 0;

            /* update the number of committed bytes. */
            ++copied_bytes;
            committed_bytes += copied_bytes;

            /* the number of copied bytes is now 0. */
            copied_bytes = 0;

            /* fix up the buffer size. */ 
            *buffer_size = committed_bytes;

            /* success. */
            retval = STATUS_SUCCESS;
            goto done;
        }

        /* edge case 1: we've run out of buffer space. */
        if (buffer_remaining == 0)
        {
            /* set the number of committed bytes. */
            committed_bytes += copied_bytes;

            /* adjust the offset. */
            br->offset += copied_bytes;

            /* reset the number of copied bytes. */
            copied_bytes = 0;

            /* fix up the buffer. */
            *bbuf = 0;

            /* fix up buffer size. */
            *buffer_size = committed_bytes;
            retval = ERROR_PSOCK_BR_READ_LINE_TRUNCATED;
            goto done;
        }

        /* edge case 2: we're out of available input. */
        if (available_input == 0)
        {
            /* update the number of committed bytes. */
            committed_bytes += copied_bytes;

            /* reset the number of copied bytes. */
            copied_bytes = 0;

            /* commit the currently copied bytes. */
            br->offset = br->current_size;

            /* attempt to fill the buffer. */
            retval = psock_br_fill(br);
            if (STATUS_SUCCESS != retval)
            {
                /* TODO - this is treated as EOL, but it may not be. */

                /* fix up the output buffer. */
                *bbuf = 0;

                /* fix up the buffer size. */ 
                ++committed_bytes;
                *buffer_size = committed_bytes;

                /* success. */
                retval = STATUS_SUCCESS;
                goto done;
            }

            /* recompute available bytes. */
            available_input = br->current_size - br->offset;

            /* reset input buffer. */
            inp = br->buffer + br->offset;
        }
    }

    /* we can't make it here. */
    RCPR_MODEL_ASSERT(false && "We can't make it here.");
    retval = ERROR_PSOCK_BR_READ_LINE_BAD_LOOP_INVARIANT;
    goto done;

done:
    return retval;
}
