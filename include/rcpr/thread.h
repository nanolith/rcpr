/**
 * \file rcpr/thread.h
 *
 * \brief Simple thread abstraction.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/resource.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief A thread represents a thread of execution, backed by the OS.
 */
typedef struct thread thread;

/**
 * \brief A thread mutex represents a mutual exclusion lock, backed by the OS.
 */
typedef struct thread_mutex thread_mutex;

/**
 * \brief A thread mutex lock represents the lock resource of a mutual exclusion
 * lock.
 *
 * This resource is modeled so it can be acquired and released in RCPR using the
 * standard resource semantics.
 */
typedef struct thread_mutex_lock thread_mutex_lock;

/**
 * \brief A function that can be executed by a \ref thread.
 *
 * \param context       The user context for this thread.
 */
typedef status (*thread_fn)(void* context);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref thread instance.
 *
 * \param th            Pointer to the \ref thread pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      thread resource.
 * \param stack_size    The size of the stack in bytes for this thread.
 * \param context       An opaque pointer to a context structure to use for this
 *                      thread instance.
 * \param fn            The function this thread should execute.
 *
 * \note This \ref thread is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref thread_resource_handle on this \ref thread instance. If the thread is
 * still executing, the resource release will block until the thread stops. It
 * is up to the caller to devise a mechanism to stop the thread.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p th must not reference a valid \ref thread instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p stack_size must be greater than zero and must follow platform rules
 *        for thread stack size.
 *      - \p fn must be a valid function.
 *
 * \post
 *      - On success, \p th is set to a pointer to a valid \ref thread instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On success, a thread of execution will begin executing \p fn.
 *      - On failure, \p th is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
thread_create(
    thread** th, allocator* a, size_t stack_size, void* context, thread_fn fn);

/**
 * \brief Create a \ref thread_mutex instance.
 *
 * \param mut           Pointer to the \ref thread_mutex pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      thread_mutex resource.
 *
 * \note This \ref thread_mutex is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * thread_mutex_resource_handle on this \ref thread_mutex instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p mut must not reference a valid \ref thread instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p mut is set to a pointer to a valid \ref thread_mutex
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p th is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
thread_mutex_create(
    thread_mutex** mut, allocator* a);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref thread instance, return the resource handle for this
 * \ref thread instance.
 *
 * \param th            The \ref thread instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref thread instance.
 */
resource* thread_resource_handle(thread* th);

/**
 * \brief Given a \ref thread_mutex instance, return the resource handle for
 * this \ref thread_mutex instance.
 *
 * \param mut           The \ref thread_mutex instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref thread_mutex instance.
 */
resource* thread_mutex_resource_handle(thread_mutex* mut);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref thread property.
 *
 * \param th            The \ref thread instance to be verified.
 *
 * \returns true if the \ref thread instance is valid.
 */
bool prop_thread_valid(const thread* th);

/**
 * \brief Valid \ref thread_mutex property.
 *
 * \param mut           The \ref thread_mutex instance to be verified.
 *
 * \returns true if the \ref thread_mutex instance is valid.
 */
bool prop_thread_mutex_valid(const thread_mutex* mut);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
