/**
 * \file rcpr/fiber.h
 *
 * \brief The RCPR fiber library.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/fiber/disciplines/management.h>
#include <rcpr/fiber/disciplines/psock_io.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>
#include <rcpr/uuid.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The fiber abstraction provides a way to capture execution so it can be
 * suspended and resumed based on yielding and scheduling events.
 */
typedef struct RCPR_SYM(fiber) RCPR_SYM(fiber);

/**
 * \brief A fiber scheduler decides which fiber to execute next on a given
 * thread of execution, by sending and receiving events to and from fiber
 * instances.
 */
typedef struct RCPR_SYM(fiber_scheduler) RCPR_SYM(fiber_scheduler);

/**
 * \brief A fiber scheduler discipline manages an API subset for both fibers and
 * the scheduler.
 */
typedef struct RCPR_SYM(fiber_scheduler_discipline)
RCPR_SYM(fiber_scheduler_discipline);

/**
 * \brief The default yield events supported by the scheduler.
 */
enum fiber_scheduler_yield_events
{
    /* Range 0x0000 to 0x0FFF are reserved for the fiber library. */
    FIBER_SCHEDULER_YIELD_EVENT_RUN                                 = 0x0000,
    FIBER_SCHEDULER_YIELD_EVENT_MAIN                                = 0x0001,
    FIBER_SCHEDULER_YIELD_EVENT_ADD_FIBER                           = 0x0002,
    FIBER_SCHEDULER_YIELD_EVENT_STOP                                = 0x0003,
    FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE                    = 0x0004,

    /* number of internal yield events. */
    FIBER_SCHEDULER_YIELD_EVENT_INTERNAL_COUNT,

    /* Range 0x1000 to 0x1FFF are reserved for the psock fiber library. */
    FIBER_SCHEDULER_YIELD_EVENT_PSOCK_BEGIN_RESERVED                = 0x1000,
    FIBER_SCHEDULER_YIELD_EVENT_PSOCK_END_RESERVED                  = 0x1FFF,
};

/**
 * \brief The default resume events supported by the scheduler.
 */
enum fiber_scheduler_resume_events
{
    /* Range 0x0000 to 0x0FFF are reserved for the fiber library. */
    FIBER_SCHEDULER_RESUME_EVENT_MAIN                               = 0x0010,
    FIBER_SCHEDULER_RESUME_EVENT_ADD_FIBER                          = 0x0011,
    FIBER_SCHEDULER_RESUME_EVENT_RUN                                = 0x0012,
    FIBER_SCHEDULER_RESUME_EVENT_RESOURCE_RELEASE                   = 0x0013,

    /* idle resume event. */
    FIBER_SCHEDULER_RESUME_EVENT_IDLE                               = 0x0020,

    /* Range 0x1000 to 0x1FFF are reserved for the psock fiber library. */
    FIBER_SCHEDULER_RESUME_EVENT_PSOCK_BEGIN_RESERVED               = 0x1000,
    FIBER_SCHEDULER_RESUME_EVENT_PSOCK_END_RESERVED                 = 0x1FFF,
};

/**
 * \brief The fiber state.
 */
enum fiber_state
{
    /** \brief The fiber has been created but hasn't started executing yet. */
    FIBER_STATE_CREATED                                             = 0x0000,

    /** \brief The fiber is either currently running or suspended. */
    FIBER_STATE_RUNNING                                             = 0x0001,

    /** \brief The fiber has been stopped and can't be resumed. */
    FIBER_STATE_STOPPED                                             = 0x0002,
};

/**
 * \brief A function that can be executed by a \ref fiber.
 *
 * \param context       The user context for this fiber.
 *
 * \returns a status code indicating success or failure when this fiber
 * terminates.
 */
typedef status (*RCPR_SYM(fiber_fn))(void* context);

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
 * When the scheduler is released, this callback is called with a yield event
 * \ref FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE.  When this occurs, the
 * scheduler callback should release all fibers and resources it has added or
 * acquired as part of its execution cycle.  When completed, it should set the
 * resume fiber to NULL and return a STATUS_SUCCESS status code. If it fails to
 * release any resources, it should return a failure code, and this will
 * be bubbled up to the caller, who should terminate the application.
 *
 * Another customary yield event is for the main thread to yield with
 * \ref FIBER_SCHEDULER_YIELD_EVENT_RUN, at which point, the fiber scheduler
 * runs all other fibers until a user event instructing it to quiesce.  This is
 * a customary event, but it is not one that the callback must implement. The
 * \ref fiber_scheduler_run function is a shortcut for entering this particular
 * yield event. This function should only be called from the main fiber.
 *
 * \param context           The user context for this \ref fiber_scheduler.
 * \param yield_fib         The yielding fiber.
 * \param yield_event       The event causing the fiber to yield.
 * \param yield_param       Pointer to the yield parameter.
 * \param resume_fib        Pointer to receive the fiber to be resumed.
 * \param resume_disc_id    Pointer to receive the pointer to the discipline id
 *                          for this restore event. Note: the stored pointer
 *                          should be GUARANTEED to outlive the life of the
 *                          fiber.
 * \param resume_event      The event causing the fiber to be resumed.
 * \param resume_param      Pointer to the resume parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when a new fiber is to be resumed.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
typedef status (*RCPR_SYM(fiber_scheduler_callback_fn))(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param, RCPR_SYM(fiber)** resume_fib,
    const RCPR_SYM(rcpr_uuid)** restore_disc_id, int *resume_event,
    void** resume_param);

/**
 * \brief A disciplined fiber scheduler callback function.
 *
 * This function is part of a vector of callbacks for a given fiber scheduler
 * discipline.  The status codes received will depend on the particular
 * discipline.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
typedef status (*RCPR_SYM(fiber_scheduler_discipline_callback_fn))(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param);

/**
 * \brief An unexpected event fiber callback function.
 *
 * An unexpected event callback can be set for a fiber. Any yielding function
 * that supports tracking unexpected events will call this callback if set to
 * notify the fiber that an unexpected or out-of-band event was encountered
 * during normal operation. If this callback returns STATUS_SUCCESS, then the
 * yielding function will retry its yield callback until it receives a valid
 * response.  If the callback returns an error code, then the yielding function
 * will return this error code to the caller.
 *
 * This functionality allows user code to handle out-of-band or unexpected
 * events in a centralized way.
 *
 * \param context                   The user context for this \ref fiber.
 * \param fib                       The fiber that received this unexpected
 *                                  message.
 * \param resume_disc_id            The discipline id that originated this
 *                                  event.
 * \param resume_event              The unexpected event code.
 * \param resume_param              An optional parameter for this unexpected
 *                                  event code.
 * \param expected_resume_disc_id   The discipline id that the caller was
 *                                  expecting.
 * \param expected_resume_event     The resume event that the caller was
 *                                  expecting.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when the yielding function should retry.
 *      - any other non-zero status code will be passed to the caller as an
 *        error code from the yielding function.
 */
typedef status (*RCPR_SYM(fiber_unexpected_event_callback_fn))(
    void* context, RCPR_SYM(fiber)* fib,
    const RCPR_SYM(rcpr_uuid)* resume_disc_id, int resume_event,
    void* resume_param, const RCPR_SYM(rcpr_uuid)* expected_resume_disc_id,
    int expected_resume_event);

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
 * \param sched         Pointer to the fiber scheduler to use for this instance.
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
RCPR_SYM(fiber_create)(
    RCPR_SYM(fiber)** fib, RCPR_SYM(allocator)* a,
    RCPR_SYM(fiber_scheduler)* sched, size_t stack_size, void* context,
    RCPR_SYM(fiber_fn) fn);

/**
 * \brief Create a \ref fiber instance for the main thread.
 *
 * \param fib           Pointer to the \ref fiber pointer to receive this
 *                      resource on success.
 * \param sched         Pointer to the fiber scheduler to use for this fiber.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber resource.
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
 *
 * \post
 *      - On success, \p fib is set to a pointer to a valid \ref fiber instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On failure, \p fib is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_create_for_thread)(
    RCPR_SYM(fiber)** fib, RCPR_SYM(fiber_scheduler)* sched,
    RCPR_SYM(allocator)* a);

/**
 * \brief Create a \ref fiber_scheduler instance.
 *
 * \param sched         Pointer to the \ref fiber_scheduler pointer to receive
 *                      this resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber_scheduler resource.
 * \param context       An opaque pointer to a context structure to use for this
 *                      \ref fiber_scheduler instance.
 * \param fn            The scheduling function for this \ref fiber_scheduler.
 *
 * \note This \ref fiber_scheduler is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * fiber_scheduler_resource_handle on this \ref fiber_scheduler instance. The
 * fiber_scheduler must be in a terminated state before releasing this resource.
 * If the fiber_scheduler is not yet terminated, then undefined behavior can
 * occur.  It is up to the caller to ensure that the fiber_scheduler has
 * terminated, such as devising a termination strategy, prior to releasing this
 * resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sched must not reference a valid \ref fiber_scheduler instance and
 *        must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p fn must be a valid function.
 *
 * \post
 *      - On success, \p sched is set to a pointer to a valid
 *        \ref fiber_scheduler instance, which is a \ref resource owned by the
 *        caller that must be released by the caller when no longer needed.
 *      - On failure, \p sched is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_create)(
    RCPR_SYM(fiber_scheduler)** sched, RCPR_SYM(allocator)* a, void* context,
    RCPR_SYM(fiber_scheduler_callback_fn) fn);

/**
 * \brief Create a disciplined \ref fiber_scheduler instance.
 *
 * \param sched         Pointer to the \ref fiber_scheduler pointer to receive
 *                      this resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber_scheduler resource.
 *
 * \note This \ref fiber_scheduler is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * fiber_scheduler_resource_handle on this \ref fiber_scheduler instance. The
 * fiber scheduler must be in a terminated state before releasing this resource.
 * If the fiber scheduler is not yet terminated, then undefined behavior can
 * occur, the least of which being that any resources owned by fibers managed by
 * this scheduler will not be released.  It is up to the caller to ensure that
 * the fiber scheduler has terminated, in this case, by making use of the
 * management discipline of the fiber scheduler.
 *
 * This is the preferred way to use the fiber library, as it is the most
 * flexible.  The \ref fiber_scheduler_create_ex method should be used for
 * specialized fiber use cases, such as simple coroutines and testing.
 *
 * This call creates a disciplined fiber scheduler, which incorporates
 * discipline domains such as I/O scheduling, fiber management, or message
 * passing. These domains can be added to a disciplined fiber scheduler
 * instance. By default, fiber management is always added to a new disciplined
 * fiber scheduler by this create function.  A new discipline should be added to
 * the fiber scheduler before using any of its methods.  This discipline should
 * be passed to the context of any fiber wishing to make use of it.  Internally,
 * the disciplined fiber scheduler will add callback vectors for each possible
 * discipline callback to its internal event router.  Only the discipline
 * instance associated with this fiber scheduler should be used to initiate
 * calls, since event codes are dynamically allocated, in order to provide a
 * flexible vectored dispatch that can accommodate user defined disciplines.
 * 
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sched must not reference a valid \ref fiber_scheduler instance and
 *        must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p sched is set to a pointer to a valid disciplined \ref
 *        fiber_scheduler instance, which is a \ref resource owned by the caller
 *        that must be released when no longer needed.
 *      - On failure, \p sched is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_create_with_disciplines)(
    RCPR_SYM(fiber_scheduler)** sched, RCPR_SYM(allocator)* a);

/**
 * \brief Create a custom fiber scheduler discipline.
 *
 * \param disc              The pointer to the pointer to receive the created
 *                          discipline on success.
 * \param id                The id for this discipline.
 * \param alloc             The allocator to use to create this discipline.
 * \param context           User context for discipline callbacks.
 * \param callbacks         The number of callbacks supported in this
 *                          discipline.
 * \param callback_vector   The array of callbacks for this discipline.
 *
 * \note On success, this creates a new discipline instance which is owned by
 * the caller. When no longer needed, the caller should release the resource
 * associated with this discipline via \ref resource_release. The resource can
 * be obtained by calling \ref fiber_scheduler_discipline_resource_handle on
 * this instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p disc must not reference a valid \ref fiber_scheduler_discipline
 *        instance and must not be NULL.
 *      - \p id must be an id unique to this discipline family (e.g. unique for
 *        all fiber I/O discipline instances, or unique for all messaging
 *        discipline instances).
 *      - \p alloc must reference a valid \ref allocator and must not be NULL.
 *      - \p callbacks must be greater than zero.
 *      - \p callback_vector must have a number of entries matching \p
 *        callbacks.
 *
 * \post
 *      - On success, \p disc is set to a pointer to a valid discipline
 *        instance, which is a \ref resource owned by the caller that must be
 *        released when no longer needed.
 *      - On failure, \p sched is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_discipline_create)(
    RCPR_SYM(fiber_scheduler_discipline)** disc, const RCPR_SYM(rcpr_uuid)* id,
    RCPR_SYM(allocator)* alloc, void* context, size_t callbacks,
    RCPR_SYM(fiber_scheduler_discipline_callback_fn)* callback_vector);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Add a fiber to the \ref fiber_scheduler.
 *
 * \param sched         The scheduler to which this \ref fiber is added.
 * \param fib           The \ref fiber to add.
 *
 * \note The \ref fiber_scheduler takes ownership of this \ref fiber and will
 * release it by calling \ref resource_release on its \ref fiber_resource_handle
 * when no longer needed.  Ultimately, it is up to the callback method for this
 * \ref fiber_scheduler to maintain ownership of this \ref fiber until it is no
 * longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance.
 *      - The caller owns \p fib.
 *
 * \post
 *      - On success, \p sched takes ownership of \p fib.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_add)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib);

/**
 * \brief Add a fiber scheduler discipline to the \ref fiber_scheduler.
 *
 * \param sched         The scheduler to which this discipline is added.
 * \param disc          The \ref fiber_scheduler_discipline to add.
 *
 * \note The \ref fiber_scheduler takes ownership of this discipline and will
 * release it by calling \ref resource_release on its
 * \ref fiber_scheduler_discipline_resource_handle when no longer needed.
 * Ultimately, it is up to the callback method for this \ref fiber_scheduler to
 * maintain ownership of this disciplineuntil it is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *      - ERROR_FIBER_SCHEDULER_DUPLICATE_DISCIPLINE_ID if an attempt is made to
 *        add a discipline with the same ID twice.
 *      - ERROR_FIBER_SCHEDULER_NOT_DISCIPLINED if an attempt is made to add a
 *        disciplined to an undisciplined fiber scheduler.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p disc is a pointer to a valid \ref fiber_scheduler_discipline
 *        instance.
 *      - The caller owns \p disc.
 *
 * \post
 *      - On success, \p sched takes ownership of \p disc.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_discipline_add)(
    RCPR_SYM(fiber_scheduler)* sched,
    RCPR_SYM(fiber_scheduler_discipline)* disc);

/**
 * \brief Find a fiber scheduler discipline in the \ref fiber_scheduler.
 *
 * \param disc          Pointer to the \ref fiber_scheduler_discipline pointer
 *                      to hold the result if found.
 * \param sched         The scheduler to search.
 * \param id            The discipline uuid to search for.
 *
 * \note The ownership of this \ref fiber_scheduler_discipline remains with the
 * scheduler, and is only valid for the lifetime of the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_FIBER_SCHEDULER_DISCIPLINE_NOT_FOUND if the discipline wasn't
 *        found in the scheduler.
 *
 * \pre
 *      - \p disc is a valid pointer to a \ref fiber_scheduler_discipline
 *        pointer.
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p id is a pointer to a valid \ref rcpr_uuid.
 *
 * \post
 *      - On success, \p disc is updated to point to a valid \ref
 *        fiber_scheduler_discipline instance owned by the scheduler.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_discipline_find)(
    RCPR_SYM(fiber_scheduler_discipline)** disc,
    RCPR_SYM(fiber_scheduler)* sched, const RCPR_SYM(rcpr_uuid)* id);

/**
 * \brief Run the fiber scheduler.
 *
 * \param sched         The scheduler to run.
 *
 * \note How the run command works is arbitrary and based on how the scheduler
 * callback operates.  The purpose of this function is to provide a shortcut to
 * calling the yield command from the current running fiber indicating that the
 * scheduler should switch into run made.  This is not strictly necessary,
 * again, depending on how the scheduler callback is written.  However, it makes
 * good sense to design the scheduler callback so that the scheduler can be
 * created, N fibers can be added by the main fiber, and then this run function
 * is called by the main fiber to start the pattern that the scheduler callback
 * has implemented.  For example, if the scheduler is implementing a reactor
 * pattern, then it will place all added fibers onto the run queue, and then
 * when these fibers need to block on async I/O, it will place them on the
 * appropriate block queues until the I/O descriptor they are blocking on
 * becomes available again.  If no fibers are available on the run queue, then
 * it would do the select / poll / epoll / kqueue operation until a descriptor
 * became available.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, at a pre-determined signal agreed upon by the scheduler
 *        callback's algorithm, run will return control to the main fiber and
 *        exit with either a success or failure return code.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_run)(
    RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Yield to the fiber scheduler.
 *
 * \param sched             The scheduler.
 * \param yield_event       The yield event.
 * \param yield_param       The yield event parameter.
 * \param resume_disc_id    Pointer to receive the pointer to the discipline id
 *                          for this restore event. Note: the stored pointer
 *                          should be GUARANTEED to outlive the life of the
 *                          fiber.
 * \param resume_event      Pointer to receive the resume event.
 * \param resume_param      Pointer to receive the resume parameter.
 *
 * \note The currently executing fiber can call yield to yield to the scheduler.
 * The yield event describes the event causing the yield; the yield parameter
 * can be used to send an optional parameter to the scheduler.  When the fiber
 * is resumed, the resume event describes why it was resumed, and the resume
 * parameter holds an optional parameter for the resume.  This can be used to
 * implement coroutines or to implement a blocking I/O simulation by yielding
 * when an I/O operation on a non-blocking socket would block.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, the scheduler will suspend this fiber and start another.
 *        As far as the fiber is concerned, it will restart when the scheduler
 *        determines that it should restart.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_yield)(
    RCPR_SYM(fiber_scheduler)* sched, int yield_event, void* yield_param,
    const RCPR_SYM(rcpr_uuid)** resume_disc_id, int* resume_event,
    void** resume_param);

/**
 * \brief Yield to the fiber scheduler through the discipline.
 *
 * \param disc          The discipline.
 * \param yield_event   The discipline yield event.
 * \param yield_param   The yield event parameter.
 * \param resume_id     Pointer to receive the discipline resume id.
 * \param resume_event  Pointer to receive the discipline resume event.
 * \param resume_param  Pointer to receive the resume parameter.
 *
 * \note The currently executing fiber can call yield to yield to the scheduler
 * through the \ref fiber_scheduler_discipline.  The discipline yield event
 * describes the event causing the yield; this is translated to a unique yield
 * event in the scheduler.  The yield parameter can be used to send an optional
 * parameter to the scheduler.  When the fiber is resumed, the resume event
 * describes why it was resumed, and the resume parameter holds an optional
 * parameter for the resume.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p disc is a pointer to a valid \ref fiber_scheduler_discipline
 *        instance.
 *
 * \post
 *      - On success, the scheduler will suspend this fiber and start another.
 *        As far as the fiber is concerned, it will restart when the scheduler
 *        determines that it should restart, which will appear as a return from
 *        this function.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_discipline_yield)(
    RCPR_SYM(fiber_scheduler_discipline)* disc, int yield_event,
    void* yield_param, const RCPR_SYM(rcpr_uuid)** resume_id, int* resume_event,
    void** resume_param);

/**
 * \brief Add an unexpected event handler to a given fiber instance.
 *
 * \param fib           The fiber to which this event handler should be added.
 * \param fn            The unexpected event handler callback function.
 * \param context       The optional context data to pass to the unexpected
 *                      event handler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p fib is a pointer to a valid \ref fiber instance.
 *      - \p fn is a pointer to a valid \ref fiber_unexpected_event_callback_fn
 *        callback function.
 *
 * \post
 *      - On success, \p fib is updated to use \p fn during an unexpected event
 *        received by participating yielding functions.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_unexpected_event_callback_add)(
    RCPR_SYM(fiber)* fib, RCPR_SYM(fiber_unexpected_event_callback_fn) fn,
    void* context);

/******************************************************************************/
/* Start of protected methods.                                                */
/*                                                                            */
/* These methods are to be used by fiber scheduler discipline handlers.       */
/******************************************************************************/

/**
 * \brief Mark the given \ref fiber as runnable.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to mark as runnable.
 * \param resume_id     The resume event's discipline id.
 * \param resume_event  The resume event for this fiber.
 * \param resume_param  The resume parameter for this fiber.
 *
 * \note It is expected that the given fiber has already been added to the
 * scheduler previously. It is an error to add an unassociated fiber to the
 * scheduler in this way.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance, previously added
 *        to the given scheduler via \ref fiber_scheduler_add.
 *
 * \post
 *      - On success, the scheduler will add the given fiber to its run queue.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_add_fiber_to_run_queue)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib,
    const RCPR_SYM(rcpr_uuid)* resume_id, int resume_event, void* resume_param);

/**
 * \brief Mark the given \ref fiber as runnable, making it the next fiber to
 * run.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to mark as runnable.
 * \param resume_id     The resume event's discipline id.
 * \param resume_event  The resume event for this fiber.
 * \param resume_param  The resume parameter for this fiber.
 *
 * \note It is expected that the given fiber has already been added to the
 * scheduler previously. It is an error to add an unassociated fiber to the
 * scheduler in this way.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance, previously added
 *        to the given scheduler via \ref fiber_scheduler_add.
 *
 * \post
 *      - On success, the scheduler will add the given fiber to its run queue.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_set_next_fiber_to_run)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib,
    const RCPR_SYM(rcpr_uuid)* resume_id, int resume_event, void* resume_param);

/**
 * \brief Set the following fiber as the idle fiber.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to set as the yield fiber.
 *
 * \note It is expected that the given fiber has already been added to the
 * scheduler previously. It is an error to add an unassociated fiber to the
 * scheduler in this way.  This fiber will be resumed with an idle event when
 * the run queue is empty.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance, previously added
 *        to the given scheduler via \ref fiber_scheduler_add.
 *
 * \post
 *      - On success, the scheduler will set the given fiber as its idle fiber.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_set_idle_fiber)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib);

/**
 * \brief Suspend this idle fiber until the scheduler idles again.
 *
 * \param sched         The scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, the fiber has been resumed normally.
 *      - On failure, either the yield failed or the fiber has been resumed due
 *        to an out-of-bound event.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_idle_fiber_yield)(
    RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Suspend this fiber until a management event is received from the
 *        disciplined fiber scheduler, and then resume this fiber with that
 *        event.
 *
 * \param sched         The scheduler.
 * \param resume_id     Pointer to receive the event's discipline id.
 * \param resume_event  Pointer to receive the resume event for this fiber.
 * \param resume_param  Pointer to receive the resume parameter for this fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p resume_event is a valid pointer to an integer value.
 *      - \p resume_param is a valid pointer to a void pointer.
 *
 * \post
 *      - On success, the fiber has been resumed with a management event.
 *      - \p resume_event is set to the management event value.
 *      - \p resume_param is set to the management event parameter.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_receive_management_event)(
    RCPR_SYM(fiber_scheduler)* sched, const RCPR_SYM(rcpr_uuid)** resume_id,
    int* resume_event, void** resume_param);

/**
 * \brief Tell the fiber scheduler to send a quiesce request to the given \ref
 *        fiber.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to instruct to quiesce.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance.
 *
 * \post
 *      - On success, the fiber has been instructed to quiesce.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_send_quiesce_request_to_fiber)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib);

/**
 * \brief Tell the fiber scheduler to send a terminate request to the given \ref
 *        fiber.
 *
 * \param sched         The scheduler.
 * \param fib           The fiber to instruct to terminate.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance.
 *
 * \post
 *      - On success, the fiber has been instructed to terminate.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_send_terminate_request_to_fiber)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib);

/**
 * \brief Tell the fiber scheduler to send a quiesce request to all running
 *        fibers.
 *
 * \param sched         The scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, all running fibers have been instructed to quiesce.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_send_quiesce_request_to_all)(
    RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Tell the fiber scheduler to send a terminate request to all running
 *        fibers.
 *
 * \param sched         The scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, all running fibers have been instructed to terminate.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_send_terminate_request_to_all)(
    RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Remove the given fiber pointer from the disciplined fiber scheduler,
 *        transferring ownership to the caller.
 *
 * \param sched         The scheduler.
 * \param fib           Pointer to fiber to be removed from the scheduler.
 *
 * \note On success, the fiber's ownership is transferred to the caller, and the
 * caller is responsible for releasing the resource associated with this fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p fib is a pointer to a valid \ref fiber instance currently owned by
 *        this scheduler.
 *
 * \post
 *      - On success, the fiber's ownership is transferred to the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_remove_fiber)(
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(fiber)* fib);

/**
 * \brief Get the main fiber from the disciplined scheduler.
 *
 * \param fib           Pointer to the pointer to hold the main fiber.
 * \param sched         The scheduler.
 *
 * \note On success, the fiber's ownership remains with the scheduler. The main
 * fiber's lifetime matches the lifetime of the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p fib is a pointer to pointer to receive the main fiber. It must not
 *        be NULL.
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *
 * \post
 *      - On success, \p fib is updated to point to the main fiber.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(disciplined_fiber_scheduler_main_fiber_get)(
    RCPR_SYM(fiber)** fib, RCPR_SYM(fiber_scheduler)* sched);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref fiber instance, return the resource handle for this
 * \ref fiber instance.
 *
 * \param fib           The \ref fiber instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref fiber instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(fiber_resource_handle)(RCPR_SYM(fiber)* fib);

/**
 * \brief Given a \ref fiber_scheduler instance, return the resource handle for
 * this \ref fiber_scheduler instance.
 *
 * \param sched         The \ref fiber_scheduler instance from which the
 *                      resource handle is returned.
 *
 * \returns the \ref resource handle for this \ref fiber_scheduler instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(fiber_scheduler_resource_handle)(RCPR_SYM(fiber_scheduler)* sched);

/**
 * \brief Given a \ref fiber_scheduler_discipline instance, return the resource
 * handle for this \ref fiber_scheduler_discipline instance.
 *
 * \param disc          The \ref fiber_scheduler_discipline instance from which
 *                      the resource handle is returned.
 *
 * \returns the \ref resource handle for this \ref fiber_scheduler_discipline
 *          instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(fiber_scheduler_discipline_resource_handle)(
    RCPR_SYM(fiber_scheduler_discipline)* disc);

/**
 * \brief Given a \ref fiber instance, return the \ref fiber_scheduler assigned
 * to that instance.
 *
 * \param fib           The \ref fiber instance from which the 
 *                      \ref fiber_scheduler instance is returned.
 *
 * \returns the \ref fiber_scheduler instance assigned to this \ref fiber
 *          instance.
 */
RCPR_SYM(fiber_scheduler)*
RCPR_SYM(fiber_scheduler_from_fiber_get)(
    RCPR_SYM(fiber)* fib);

/**
 * \brief Given a \ref fiber instance, return its current state.
 *
 * \param fib           The \ref fiber instance.
 *
 * \returns the fiber state, one of the values in the \ref fiber_state
 * enumeration.
 */
uint64_t RCPR_SYM(fiber_state_get)(const RCPR_SYM(fiber)* fib);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref fiber property.
 *
 * \param fib           The \ref fiber instance to be verified.
 *
 * \returns true if the \ref fiber instance is valid.
 */
bool RCPR_SYM(prop_fiber_valid)(const RCPR_SYM(fiber)* fib);

/**
 * \brief Valid \ref fiber_scheduler property.
 *
 * \param sched         The \ref fiber_scheduler instance to be verified.
 *
 * \returns true if the \ref fiber_scheduler instance is valid.
 */
bool RCPR_SYM(prop_fiber_scheduler_valid)(
    const RCPR_SYM(fiber_scheduler)* sched);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_fiber_as(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(fiber) sym ## _ ## fiber; \
    typedef RCPR_SYM(fiber_scheduler) sym ## _ ## fiber_scheduler; \
    typedef RCPR_SYM(fiber_scheduler_discipline) \
    sym ## _ ## fiber_scheduler_discipline; \
    typedef RCPR_SYM(fiber_fn) sym ## _ ## fiber_fn; \
    typedef RCPR_SYM(fiber_scheduler_callback_fn) \
    sym ## _ ## fiber_scheduler_callback_fn; \
    typedef RCPR_SYM(fiber_scheduler_discipline_callback_fn) \
        sym ## _ ## fiber_scheduler_discipline_callback_fn; \
    typedef RCPR_SYM(fiber_unexpected_event_callback_fn) \
        sym ## _ ## fiber_unexpected_event_callback_fn; \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## fiber_create( \
        RCPR_SYM(fiber)** u, RCPR_SYM(allocator)* v, \
        RCPR_SYM(fiber_scheduler)* w, size_t x, void* y, \
        RCPR_SYM(fiber_fn) z) { \
            return RCPR_SYM(fiber_create)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_create_for_thread( \
        RCPR_SYM(fiber)** x, RCPR_SYM(fiber_scheduler)* y, \
        RCPR_SYM(allocator)* z) { \
            return RCPR_SYM(fiber_create_for_thread)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_create( \
        RCPR_SYM(fiber_scheduler)** w, RCPR_SYM(allocator)* x, void* y, \
        RCPR_SYM(fiber_scheduler_callback_fn) z) { \
            return RCPR_SYM(fiber_scheduler_create)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_create_with_disciplines( \
        RCPR_SYM(fiber_scheduler)** x, RCPR_SYM(allocator)* y) { \
            return RCPR_SYM(fiber_scheduler_create_with_disciplines)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_discipline_create( \
        RCPR_SYM(fiber_scheduler_discipline)** u, \
        const RCPR_SYM(rcpr_uuid)* v, RCPR_SYM(allocator)* w, void* x, \
        size_t y, RCPR_SYM(fiber_scheduler_discipline_callback_fn)* z) { \
            return RCPR_SYM(fiber_scheduler_discipline_create)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_add( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return RCPR_SYM(fiber_scheduler_add)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_discipline_add( \
        RCPR_SYM(fiber_scheduler)* x, \
        RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(fiber_scheduler_discipline_add)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_discipline_find( \
        RCPR_SYM(fiber_scheduler_discipline)** x, \
        RCPR_SYM(fiber_scheduler)* y, const RCPR_SYM(rcpr_uuid)* z) { \
            return RCPR_SYM(fiber_scheduler_discipline_find(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_run( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return RCPR_SYM(fiber_scheduler_run)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_scheduler_yield( \
        RCPR_SYM(fiber_scheduler)* u, int v, void* w, \
        const RCPR_SYM(rcpr_uuid)** x, int* y, void** z) { \
            return RCPR_SYM(fiber_scheduler_yield)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_discipline_yield( \
        RCPR_SYM(fiber_scheduler_discipline)* u, int v, void* w, \
        const RCPR_SYM(rcpr_uuid)** x, int* y, void** z) { \
            return RCPR_SYM(fiber_discipline_yield)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## fiber_unexpected_event_callback_add( \
        RCPR_SYM(fiber)* x, RCPR_SYM(fiber_unexpected_event_callback_fn) y, \
        void* z) { \
            return RCPR_SYM(fiber_unexpected_event_callback_add)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_add_fiber_to_run_queue( \
        RCPR_SYM(fiber_scheduler)* v, RCPR_SYM(fiber)* w, \
        const RCPR_SYM(rcpr_uuid)* x, int y, void* z) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_add_fiber_to_run_queue)( \
                    v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_set_next_fiber_to_run( \
        RCPR_SYM(fiber_scheduler)* v, RCPR_SYM(fiber)* w, \
        const RCPR_SYM(rcpr_uuid)* x, int y, void* z) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_set_next_fiber_to_run)( \
                    v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_set_idle_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_set_idle_fiber)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_idle_fiber_yield( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_idle_fiber_yield)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_receive_management_event( \
        RCPR_SYM(fiber_scheduler)* w, const RCPR_SYM(rcpr_uuid)** x, int* y, \
        void** z) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_receive_management_event)(\
                    w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_send_quiesce_request_to_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return \
                RCPR_SYM( \
                    disciplined_fiber_scheduler_send_quiesce_request_to_fiber)(\
                        x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_send_terminate_request_to_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return \
                RCPR_SYM( \
                  disciplined_fiber_scheduler_send_terminate_request_to_fiber)(\
                        x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_send_quiesce_request_to_all( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return \
                RCPR_SYM(\
                    disciplined_fiber_scheduler_send_quiesce_request_to_all)( \
                        x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_send_terminate_request_to_all( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return \
                RCPR_SYM( \
                    disciplined_fiber_scheduler_send_terminate_request_to_all)(\
                        x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_remove_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return RCPR_SYM(disciplined_fiber_scheduler_remove_fiber)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## disciplined_fiber_scheduler_main_fiber_get( \
        RCPR_SYM(fiber)** x, RCPR_SYM(fiber_scheduler)* y) { \
            return RCPR_SYM(disciplined_fiber_scheduler_main_fiber_get)(x,y); }\
    static inline RCPR_SYM(resource)* sym ## _ ## fiber_resource_handle( \
        RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(fiber_resource_handle)(x); } \
    static inline RCPR_SYM(resource)* \
    sym ## _ ## fiber_scheduler_resource_handle( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return RCPR_SYM(fiber_scheduler_resource_handle)(x); } \
    static inline RCPR_SYM(resource)* \
    sym ## _ ## fiber_scheduler_discipline_resource_handle( \
        RCPR_SYM(fiber_scheduler_discipline)* x) { \
            return RCPR_SYM(fiber_scheduler_discipline_resource_handle)(x); } \
    static inline uint64_t sym ## _ ## fiber_state_get( \
        const RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(fiber_state_get)(x); } \
    static inline RCPR_SYM(fiber_scheduler)* \
    sym ## _ ## fiber_scheduler_from_fiber_get( \
        RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(fiber_scheduler_from_fiber_get)(x); } \
    static inline bool sym ## _ ## prop_fiber_valid( \
        const RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(prop_fiber_valid)(x); } \
    static inline bool sym ## _ ## prop_fiber_scheduler_valid( \
        const RCPR_SYM(fiber_scheduler)* x) { \
            return RCPR_SYM(prop_fiber_scheduler_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_fiber \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(fiber) fiber; \
    typedef RCPR_SYM(fiber_scheduler) fiber_scheduler; \
    typedef RCPR_SYM(fiber_scheduler_discipline) fiber_scheduler_discipline; \
    typedef RCPR_SYM(fiber_fn) fiber_fn; \
    typedef RCPR_SYM(fiber_scheduler_callback_fn) fiber_scheduler_callback_fn; \
    typedef RCPR_SYM(fiber_scheduler_discipline_callback_fn) \
        fiber_scheduler_discipline_callback_fn; \
    typedef RCPR_SYM(fiber_unexpected_event_callback_fn) \
        fiber_unexpected_event_callback_fn; \
    static inline status FN_DECL_MUST_CHECK fiber_create( \
        RCPR_SYM(fiber)** u, RCPR_SYM(allocator)* v, \
        RCPR_SYM(fiber_scheduler)* w, size_t x, void* y, \
        RCPR_SYM(fiber_fn) z) { \
            return RCPR_SYM(fiber_create)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK fiber_create_for_thread( \
        RCPR_SYM(fiber)** x, RCPR_SYM(fiber_scheduler)* y, \
        RCPR_SYM(allocator)* z) { \
            return RCPR_SYM(fiber_create_for_thread)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_create( \
        RCPR_SYM(fiber_scheduler)** w, RCPR_SYM(allocator)* x, void* y, \
        RCPR_SYM(fiber_scheduler_callback_fn) z) { \
            return RCPR_SYM(fiber_scheduler_create)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    fiber_scheduler_create_with_disciplines( \
        RCPR_SYM(fiber_scheduler)** x, RCPR_SYM(allocator)* y) { \
            return RCPR_SYM(fiber_scheduler_create_with_disciplines)(x,y); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_discipline_create( \
        RCPR_SYM(fiber_scheduler_discipline)** u, \
        const RCPR_SYM(rcpr_uuid)* v, RCPR_SYM(allocator)* w, void* x, \
        size_t y, RCPR_SYM(fiber_scheduler_discipline_callback_fn)* z) { \
            return RCPR_SYM(fiber_scheduler_discipline_create)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_add( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return RCPR_SYM(fiber_scheduler_add)(x,y); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_discipline_add( \
        RCPR_SYM(fiber_scheduler)* x, \
        RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(fiber_scheduler_discipline_add)(x,y); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_discipline_find( \
        RCPR_SYM(fiber_scheduler_discipline)** x, \
        RCPR_SYM(fiber_scheduler)* y, const RCPR_SYM(rcpr_uuid)* z) { \
            return RCPR_SYM(fiber_scheduler_discipline_find)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_run( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return RCPR_SYM(fiber_scheduler_run)(x); } \
    static inline status FN_DECL_MUST_CHECK fiber_scheduler_yield( \
        RCPR_SYM(fiber_scheduler)* u, int v, void* w, \
        const RCPR_SYM(rcpr_uuid)** x, int* y, void** z) { \
            return RCPR_SYM(fiber_scheduler_yield)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK fiber_discipline_yield( \
        RCPR_SYM(fiber_scheduler_discipline)* u, int v, void* w, \
        const RCPR_SYM(rcpr_uuid)** x, int* y, void** z) { \
            return RCPR_SYM(fiber_discipline_yield)(u,v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    fiber_unexpected_event_callback_add( \
        RCPR_SYM(fiber)* x, RCPR_SYM(fiber_unexpected_event_callback_fn) y, \
        void* z) { \
            return RCPR_SYM(fiber_unexpected_event_callback_add)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_add_fiber_to_run_queue( \
        RCPR_SYM(fiber_scheduler)* v, RCPR_SYM(fiber)* w, \
        const RCPR_SYM(rcpr_uuid)* x, int y, void* z) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_add_fiber_to_run_queue)( \
                    v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_set_next_fiber_to_run( \
        RCPR_SYM(fiber_scheduler)* v, RCPR_SYM(fiber)* w, \
        const RCPR_SYM(rcpr_uuid)* x, int y, void* z) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_set_next_fiber_to_run)( \
                    v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_set_idle_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_set_idle_fiber)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_idle_fiber_yield( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_idle_fiber_yield)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_receive_management_event( \
        RCPR_SYM(fiber_scheduler)* w, const RCPR_SYM(rcpr_uuid)** x, int* y, \
        void** z) { \
            return \
                RCPR_SYM(disciplined_fiber_scheduler_receive_management_event)(\
                    w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_send_quiesce_request_to_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return \
                RCPR_SYM( \
                    disciplined_fiber_scheduler_send_quiesce_request_to_fiber)(\
                        x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_send_terminate_request_to_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return \
                RCPR_SYM( \
                  disciplined_fiber_scheduler_send_terminate_request_to_fiber)(\
                        x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_send_quiesce_request_to_all( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return \
                RCPR_SYM(\
                    disciplined_fiber_scheduler_send_quiesce_request_to_all)( \
                        x); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_send_terminate_request_to_all( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return \
                RCPR_SYM( \
                    disciplined_fiber_scheduler_send_terminate_request_to_all)(\
                        x); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_remove_fiber( \
        RCPR_SYM(fiber_scheduler)* x, RCPR_SYM(fiber)* y) { \
            return RCPR_SYM(disciplined_fiber_scheduler_remove_fiber)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    disciplined_fiber_scheduler_main_fiber_get( \
        RCPR_SYM(fiber)** x, RCPR_SYM(fiber_scheduler)* y) { \
            return RCPR_SYM(disciplined_fiber_scheduler_main_fiber_get)(x,y); }\
    static inline RCPR_SYM(resource)* fiber_resource_handle( \
        RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(fiber_resource_handle)(x); } \
    static inline RCPR_SYM(resource)* fiber_scheduler_resource_handle( \
        RCPR_SYM(fiber_scheduler)* x) { \
            return RCPR_SYM(fiber_scheduler_resource_handle)(x); } \
    static inline RCPR_SYM(resource)* \
    fiber_scheduler_discipline_resource_handle( \
        RCPR_SYM(fiber_scheduler_discipline)* x) { \
            return RCPR_SYM(fiber_scheduler_discipline_resource_handle)(x); } \
    static inline uint64_t fiber_state_get( \
        const RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(fiber_state_get)(x); } \
    static inline RCPR_SYM(fiber_scheduler)* fiber_scheduler_from_fiber_get( \
        RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(fiber_scheduler_from_fiber_get)(x); } \
    static inline bool prop_fiber_valid( \
        const RCPR_SYM(fiber)* x) { \
            return RCPR_SYM(prop_fiber_valid)(x); } \
    static inline bool prop_fiber_scheduler_valid( \
        const RCPR_SYM(fiber_scheduler)* x) { \
            return RCPR_SYM(prop_fiber_scheduler_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
