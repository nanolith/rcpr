/**
 * \file platform/pthread/thread/thread_cond_wait.c
 *
 * \brief Wait (block) on a condition variable.
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
 * \brief Wait on a condition variable, using the given mutex for exclusivity.
 *
 * \param lock          Pointer to the \ref thread_mutex_lock pointer to be
 *                      released while waiting on the condition variable, and
 *                      re-acquired once signaled.
 * \param cond          The \ref thread_cond variable on which to wait.
 *
 * \note The \ref thread_mutex_lock resource is released while the thread waits
 * on the condition variable and re-acquired once the condition variable has
 * been signaled.  The caller maintains ownership of the \ref thread_mutex_lock,
 * although the pointer may have changed, and must release it when it is no
 * longer needed by calling \ref resource_release on its resource handle.  The
 * resource handle can be accessed by calling
 * \ref thread_mutex_lock_resource_handle on this \ref thread_mutex_lock
 * instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p lock must be an acquired lock from a \ref thread_mutex and must not
 *        be NULL.
 *      - \p cond must reference a valid \ref thread_cond and must not be NULL.
 *
 * \post
 *      - On success, \p lock is set to a pointer to a valid
 *        \ref thread_mutex_lock instance, which is a \ref resource owned by the
 *        caller that must be released by the caller when no longer needed.
 *      - On failure, \p lock is unchanged.
 */
status FN_DECL_MUST_CHECK
thread_cond_wait(
    thread_mutex_lock** lock, thread_cond* cond)
{
    int retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != lock);
    MODEL_ASSERT(prop_thread_mutex_lock_valid(*lock));
    MODEL_ASSERT(prop_thread_cond_valid(cond));

    /* wait on the condition variable. */
    retval = pthread_cond_wait(&(cond->cond), &((*lock)->parent->mutex));
    if (STATUS_SUCCESS != retval)
    {
        return ERROR_THREAD_COND_WAIT;
    }

    /* success. */
    return STATUS_SUCCESS;
}
