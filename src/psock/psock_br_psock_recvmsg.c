/**
 * \file psock/psock_br_psock_recvmsg.c
 *
 * \brief Receive a message from the given \ref psock instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Receive a message from the \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to receive a message.
 * \param ctx           User context (ignored).
 * \param msg           Pointer to the message header to populate.
 * \param len           The maximum length of the message.
 * \param flags         The flags to use when sending the message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_br_psock_recvmsg)(
    RCPR_SYM(psock)* sock, void* ctx, struct msghdr* msg, size_t* len,
    int flags)
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

    /* verify that recvmsg is defined. */
    if (NULL == wrapped_vtable->recvmsg_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    /* pass through to the wrapped socket. */
    return
        wrapped_vtable->recvmsg_fn(
            br->wrapped, br->wrapped->context, msg, len, flags);
}
