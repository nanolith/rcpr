/**
 * \file rcpr/fiber_fwd.h
 *
 * \brief Forward declarations for fiber library.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward declaration for fiber. */
struct fiber;

/**
 * \brief The fiber abstraction provides a way to capture execution so it can be
 * suspended and resumed based on yielding and scheduling events.
 */
typedef struct fiber fiber;

/* forward declaration for fiber_scheduler. */
struct fiber_scheduler;

/**
 * \brief The fiber scheduler abstraction provides a way to schedule captured
 * units of execution (\ref fibers) so that these can be suspended and resumed
 * based on yielding and scheduling events.
 */
typedef struct fiber_scheduler fiber_scheduler;

/* forward declaration for fiber_scheduler_callback_fn. */
typedef status (*fiber_scheduler_callback_fn)(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, int *resume_event, void** resume_param);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
