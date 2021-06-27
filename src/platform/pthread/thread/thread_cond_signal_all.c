/**
 * \file platform/pthread/thread/thread_cond_signal_all.c
 *
 * \brief Signal all threads waiting on this condition variable to wake.
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
 * \brief Notify all threads waiting on the condition variable.
 *
 * \param cond          The \ref thread_cond variable to signal.
 *
 * This method notifies all threads waiting on the given condition variable
 * to wake.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p cond must be a valid \ref thread_cond variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, all threads waiting on the given condition variable
 *        will be signaled and will wake.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(thread_cond_signal_all)(
    RCPR_SYM(thread_cond)* cond)
{
    int retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_thread_cond_valid(cond));

    /* signal all threads waiting on this conditional. */
    retval = pthread_cond_broadcast(&(cond->cond));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* success. */
    return STATUS_SUCCESS;
}
