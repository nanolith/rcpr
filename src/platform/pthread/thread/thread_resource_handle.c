/**
 * \file platform/pthread/thread/thread_resource_handle.c
 *
 * \brief Get the resource handle for a thread.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "thread_internal.h"

RCPR_IMPORT_thread;

/**
 * \brief Given a \ref thread instance, return the resource handle for this
 * \ref thread instance.
 *
 * \param th            The \ref thread instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref thread instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(thread_resource_handle)(
    RCPR_SYM(thread)* th)
{
    RCPR_MODEL_ASSERT(prop_thread_valid(th));

    return &(th->hdr);
}
