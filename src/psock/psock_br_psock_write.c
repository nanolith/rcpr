/**
 * \file psock/psock_br_psock_write.c
 *
 * \brief Write data to a descriptor.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param ctx           User context (ignored).
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_br_psock_write)(
    RCPR_SYM(psock)* sock, void* ctx, const void* data, size_t* size)
{
    (void)ctx;
    status retval;
    const psock_vtable* wrapped_vtable;
    psock_br* br = (psock_br*)sock;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(br));

    /* get the wrapped socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&wrapped_vtable,
            psock_resource_handle(br->wrapped));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* pass through to the wrapped socket. */
    return
        wrapped_vtable->write_fn(br->wrapped, br->wrapped->context, data, size);
}
