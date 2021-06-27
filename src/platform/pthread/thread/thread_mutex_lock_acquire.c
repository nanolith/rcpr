/**
 * \file platform/pthread/thread/thread_mutex_lock_acquire.c
 *
 * \brief Acquire a lock on a \ref thread_mutex.
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
 * \brief Acquire the lock from a \ref thread_mutex.
 *
 * \param lock          Pointer to the \ref thread_mutex_lock pointer to receive
 *                      this resource on success.
 * \param mut           The \ref thread_mutex from which this lock should be
 *                      acquired.
 *
 * \note This \ref thread_mutex_lock is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * thread_mutex_lock_resource_handle on this \ref thread_mutex_lock instance.
 *
 * The lock can only be acquired by one thread at a time. This function blocks
 * until the lock can be acquired.  It is an error to acquire the same lock
 * multiple times without releasing it first, and it will cause a deadlock for
 * the calling thread.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p lock must not reference a valid \ref thread_mutex_lock instance and
 *        must not be NULL.
 *      - \p mut must reference a valid \ref thread_mutex and must not be NULL.
 *
 * \post
 *      - On success, \p lock is set to a pointer to a valid
 *        \ref thread_mutex_lock instance, which is a \ref resource owned by the
 *        caller that must be released by the caller when no longer needed.
 *      - On failure, \p lock is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(thread_mutex_lock_acquire)(
    RCPR_SYM(thread_mutex_lock)** lock, RCPR_SYM(thread_mutex)* mut)
{
    int retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != lock);
    RCPR_MODEL_ASSERT(prop_thread_mutex_valid(mut));
    RCPR_MODEL_ASSERT(prop_thread_mutex_lock_valid(&mut->child));

    /* acquire the lock. */
    retval = pthread_mutex_lock(&mut->mutex);
    if (STATUS_SUCCESS != retval)
    {
        return ERROR_THREAD_MUTEX_LOCK;
    }

    /* return the lock instance. */
    *lock = &mut->child;

    /* success. */
    return STATUS_SUCCESS;
}
