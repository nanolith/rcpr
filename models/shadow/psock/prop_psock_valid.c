/**
 * \file models/shadow/psock/prop_psock_valid.c
 *
 * \brief Check whether a psock instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/psock/psock_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);

/**
 * \brief Valid \ref psock property.
 *
 * \param sock          The \ref psock instance to be verified.
 *
 * \returns true if the \ref psock instance is valid.
 */
bool prop_psock_valid(const psock* sock)
{
    MODEL_ASSERT(NULL != sock);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        sock->MODEL_STRUCT_TAG_REF(psock), psock);

    return
        prop_resource_valid(psock_resource_handle(sock))
     && prop_allocator_valid(sock->alloc)
     && NULL != sock->read_fn
     && NULL != sock->write_fn;
}
