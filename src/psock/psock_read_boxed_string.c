/**
 * \file psock/psock_read_boxed_string.c
 *
 * \brief Read a boxed string value from a \ref psock instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_string.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      value.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.  On success, this pointer is updated to a
 *                      string value that is owned by the caller and must be
 *                      released to the allocator when no longer needed.
 * \param length        Pointer to a variable to be set to the length of this
 *                      string on success.
 *
 * The \ref psock_write_boxed_string method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a C-string
 * value.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p a must be a pointer to a valid \ref allocator instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid C-string variable and must not be
 *        NULL.
 *      - \p length must be a pointer to a size_t value and must not be NULL.
 *
 * \post
 *      - On success, \p val is set to the C-string value read from the socket
 *        and unboxed.
 *      - On success, \p length is set to the length of the C-string.
 *      - On failure, \p val is unchanged and an error status is returned.
 *      - On failure, \p length is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_string)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, char** val, size_t* length)
{
    status retval, release_retval;
    const psock_vtable* sock_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(NULL != val);
    RCPR_MODEL_ASSERT(NULL != length);

    /* attempt to read the type from the socket. */
    uint32_t type = 0U;
    retval = psock_read_raw_uint32(sock, &type);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* verify that the type matches what we expect. */
    if (PSOCK_BOXED_TYPE_STRING != type)
    {
        retval = ERROR_PSOCK_READ_BOXED_INVALID_TYPE;
        goto done;
    }

    /* attempt to read the size from the socket. */
    uint32_t size = 0U;
    retval = psock_read_raw_uint32(sock, &size);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* verify that the size is a sane value. */
    if (UINT32_MAX == size)
    {
        retval = ERROR_PSOCK_READ_BOXED_INVALID_SIZE;
        goto done;
    }

    /* allocate size bytes for the data. */
    char* buffer = NULL;
    retval = allocator_allocate(a, (void**)&buffer, size + 1);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* ASCIIZ the string buffer. */
    buffer[size] = 0;

    /* get the socket's vtable. */
    sock_vtable =
        (const psock_vtable*)resource_vtable_get(psock_resource_handle(sock));

    /* read data to the buffer. */
    size_t read_size = size;
    retval =
        sock_vtable->read_fn(sock, sock->context, buffer, &read_size, true);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_buffer;
    }

    /* verify read size. */
    if (read_size != size)
    {
        retval = ERROR_PSOCK_READ_INVALID_SIZE;
        goto cleanup_buffer;
    }

    /* on success, update output parameters. */
    *val = buffer;
    *length = size;
    goto done;

cleanup_buffer:
    release_retval = allocator_reclaim(a, buffer);
    if (STATUS_SUCCESS == retval && STATUS_SUCCESS != release_retval)
    {
        /* cascade error if deallocation fails. */
        retval = release_retval;
    }

done:
    return retval;
}
