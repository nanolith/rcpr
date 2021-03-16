/**
 * \file fiber/common/fiber_scheduler_run.c
 *
 * \brief Run the fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

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
fiber_scheduler_run(
    fiber_scheduler* sched)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* call the callback function to run the scheduler. */
    int resume_event;
    void* resume_param;
    return
        fiber_scheduler_yield(
            sched, FIBER_SCHEDULER_YIELD_EVENT_RUN, NULL,
            &resume_event, &resume_param);
}
