/**
 * \file platform/pthread/thread/thread_mutex_resource_handle.c
 *
 * \brief Get the resource handle for a mutex.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "thread_internal.h"

/**
 * \brief Given a \ref thread_mutex instance, return the resource handle for
 * this \ref thread_mutex instance.
 *
 * \param mut           The \ref thread_mutex instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref thread_mutex instance.
 */
RCPR_SYM(resource)* thread_mutex_resource_handle(thread_mutex* mut)
{
    MODEL_ASSERT(prop_thread_mutex_valid(mut));

    return &(mut->hdr);
}
