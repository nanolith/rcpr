/**
 * \file rcpr/fiber.h
 *
 * \brief The RCPR fiber library.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The fiber abstraction provides a way to capture execution so it can be
 * suspended and resumed based on yielding and scheduling events.
 */
typedef struct fiber fiber;

/**
 * \brief A fiber scheduler decides which fiber to execute next on a given
 * thread of execution, by sending and receiving events to and from fiber
 * instances.
 */
typedef struct fiber_scheduler fiber_scheduler;

/**
 * \brief A function that can be executed by a \ref fiber.
 *
 * \param context       The user context for this fiber.
 *
 * \returns a status code indicating success or failure when this fiber
 * terminates.
 */
typedef status (*fiber_fn)(void* context);

/**
 * \brief A fiber scheduler callback function.
 *
 * This function receives events from fibers and can send events to a fiber it
 * resumes. This function is responsible for queuing fibers and for returning
 * control to the main thread. How this is done is user-defined behavior.
 *
 * When the scheduler is first created, the very first fiber given to this
 * scheduler callback function is the main thread's fiber. This is a special
 * fiber that is owned by the \ref fiber_scheduler instance and must not be
 * released by this callback.  This fiber will be provided as the yield fiber
 * with a yield event \ref FIBER_SCHEDULER_YIELD_EVENT_MAIN.  When this occurs,
 * the scheduler should cache this main thread somewhere in its user context and
 * it should resume the main thread immediately with the event \ref
 * FIBER_SCHEDULER_RESUME_EVENT_MAIN.
 *
 * Each time a new fiber is added to the scheduler, this callback function will
 * be called. The yielding fiber will be the caller's fiber, and its yield
 * event will be \ref FIBER_SCHEDULER_YIELD_EVENT_ADD_FIBER.  The yield_param
 * will be the new fiber being added. The scheduler can follow any user-defined
 * strategy for running this fiber. Eventually, the calling fiber should be
 * resumed with the \ref FIBER_SCHEDULER_RESUME_EVENT_ADD_FIBER event.  At this
 * point, this function and user context takes ownership of the fiber and is
 * expected to release it when no longer in use, or pass this fiber to some
 * other owner based on its scheduling strategy. The \ref fiber_scheduler_add
 * function is a shortcut for performing this action. This function can be
 * called from any fiber.
 *
 * Another customary yield event is for the main thread to yield with
 * \ref FIBER_SCHEDULER_YIELD_EVENT_RUN, at which point, the fiber scheduler
 * runs all other fibers until a user event instructing it to quiesce.  This is
 * a customary event, but it is not one that the callback must implement. The
 * \ref fiber_scheduler_run function is a shortcut for entering this particular
 * yield event. This function should only be called from the main fiber.
 *
 * \param context       The user context for this \ref fiber_scheduler.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 * \param resume_fib    Pointer to receive the fiber to be resumed.
 * \param resume_event  The event causing the fiber to be resumed.
 * \param resume_param  Pointer to the resume parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when a new fiber is to be resumed.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
typedef status (*fiber_scheduler_callback_fn)(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, int resume_event, void* resume_param);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref fiber instance.
 *
 * \param fib           Pointer to the \ref fiber pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber resource.
 * \param stack_size    The size of the stack in bytes for this fiber.
 * \param context       An opaque pointer to a context structure to use for this
 *                      \ref fiber instance.
 * \param fn            The function this \ref fiber should execute.
 *
 * \note This \ref fiber is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref fiber_resource_handle on this \ref fiber instance. The fiber must be in
 * a terminated state before releasing this resource. If the fiber is
 * not yet terminated, then the resource release will fail. It
 * is up to the caller to ensure that the fiber has terminated, such as devising
 * a termination strategy, prior to releasing this resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p fib must not reference a valid \ref fiber instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p stack_size must be greater than zero and must follow platform rules
 *        for fiber stack size.
 *      - \p fn must be a valid function.
 *
 * \post
 *      - On success, \p fib is set to a pointer to a valid \ref fiber instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On failure, \p fib is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
fiber_create(
    fiber** fib, allocator* a, size_t stack_size, void* context, fiber_fn fn);

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
