/**
 * \file platform/pthread/thread/thread_cond_signal_one.c
 *
 * \brief Signal a single thread waiting on this condition variable to wake.
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
 * \brief Notify a single thread waiting on the condition variable.
 *
 * \param cond          The \ref thread_cond variable to signal.
 *
 * This method notifies a single thread waiting on the given condition variable
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
 *      - On success, a single thread waiting on the given condition variable
 *        will be signaled and will wake.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(thread_cond_signal_one)(
    RCPR_SYM(thread_cond)* cond)
{
    int retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_thread_cond_valid(cond));

    /* signal a single thread waiting on this conditional. */
    retval = pthread_cond_signal(&(cond->cond));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* success. */
    return STATUS_SUCCESS;
}
