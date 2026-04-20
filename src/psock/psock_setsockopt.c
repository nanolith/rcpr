/**
 * \file psock/psock_setsockopt.c
 *
 * \brief Set socket options for \ref psock instances that support this feature.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <sys/socket.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_resource;

/**
 * \brief Set socket options for \ref psock instances that support this feature.
 *
 * This method roughly corresponds to the POSIX setsockopt function.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param level         The protocol level at which this option resides.
 * \param option_name   The option to set.
 * \param option_value  The value to which this option is set.
 * \param option_len    The length of this option value in bytes.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p ctx must be a pointer to the user context or NULL.
 *      - \p level must be a valid protocol level argument (e.g. SOL_SOCKET).
 *      - \p option_value must be a valid pointer to data dependent on the
 *        option requirements.
 *      - \p option_len must be the size of \p option_value in bytes.
 *
 * \post
 *      - On success, STATUS_SUCCESS is returned.
 *      - On failure, an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_setsockopt)(
    RCPR_SYM(psock)* sock, int level, int option_name, const void* option_value,
    socklen_t option_len)
{
    status retval;
    const psock_vtable* sock_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != option_value);

    /* get the socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&sock_vtable, psock_resource_handle(sock));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify that setsockopt_fn is defined. */
    if (NULL == sock_vtable->setsockopt_fn)
    {
        return ERROR_PSOCK_METHOD_UNDEFINED;
    }

    return
        sock_vtable->setsockopt_fn(
            sock, sock->context, level, option_name, option_value, option_len);
}
