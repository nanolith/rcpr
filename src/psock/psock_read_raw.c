/**
 * \file psock/psock_read_raw.c
 *
 * \brief Read a raw value from a \ref psock instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

/**
 * \brief Attempt to read up to \p data_size bytes from the psock instance. This
 * function will return fewer bytes (updating \p data_size accordingly) if no
 * more bytes are currently available.  In this case, this function will return
 * \ref ERROR_PSOCK_READ_WOULD_BLOCK, and it's up to the caller to decide
 * whether to block on more bytes by calling \ref psock_read_block.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param data          Pointer to a buffer that can accept up to \p data_size
 *                      bytes.  This must be a valid buffer.
 * \param data_size     Size of the data to read. Set to the number of bytes to
 *                      read by the caller, and updated to the number of bytes
 *                      actually read by the successful execution of this
 *                      function.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_PSOCK_READ_WOULD_BLOCK if reading more data would block.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid buffer that is at least
 *        \p data_size bytes in length.
 *      - \p data_size must be a pointer to a valid size argument, set to the
 *        size of the \p data buffer.
 *
 * \post
 *      - On success, \p data contains the bytes written, and \p data_size is
 *        set to the number of bytes written.
 *      - On failure, \p data is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
psock_read_raw(
    psock* sock, void* data, size_t* data_size)
{
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != data);
    MODEL_ASSERT(NULL != data_size);
    MODEL_ASSERT(*data_size > 0);
    MODEL_ASSERT(prop_valid_range(data, *data_size));

    /* read data to the buffer. */
    size_t read_size = *data_size;
    retval = sock->read_fn(sock, data, &read_size, true);
    if (ERROR_PSOCK_READ_WOULD_BLOCK == retval)
    {
        retval = STATUS_SUCCESS;
    }
    else if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* on success, update output parameter. */
    *data_size = read_size;
    goto done;

done:
    return retval;

}
