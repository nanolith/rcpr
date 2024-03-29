/**
 * \file platform/pthread/thread/thread_cond_resource_handle.c
 *
 * \brief Get the resource handle for a condition variable.
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
 * \brief Given a \ref thread_cond instance, return the resource handle for
 * this \ref thread_cond instance.
 *
 * \param mut           The \ref thread_cond instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref thread_cond instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(thread_cond_resource_handle)(
    RCPR_SYM(thread_cond)* cond)
{
    RCPR_MODEL_ASSERT(prop_thread_cond_valid(cond));

    return &(cond->hdr);
}
