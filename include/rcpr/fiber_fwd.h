/**
 * \file rcpr/fiber_fwd.h
 *
 * \brief Forward declarations for fiber library.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
#include <rcpr/uuid.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The fiber abstraction provides a way to capture execution so it can be
 * suspended and resumed based on yielding and scheduling events.
 */
typedef struct RCPR_SYM(fiber) RCPR_SYM(fiber);

/**
 * \brief The fiber scheduler abstraction provides a way to schedule captured
 * units of execution (\ref fibers) so that these can be suspended and resumed
 * based on yielding and scheduling events.
 */
typedef struct RCPR_SYM(fiber_scheduler) RCPR_SYM(fiber_scheduler);

/**
 * \brief The fiber scheduler discipline abstraction provides a way to manage a
 * subset of fiber messages as a protocol for the overall fiber messaging API.
 */
typedef struct RCPR_SYM(fiber_scheduler_discipline)
RCPR_SYM(fiber_scheduler_discipline);

/* forward declaration for fiber_scheduler_callback_fn. */
typedef status (*RCPR_SYM(fiber_scheduler_callback_fn))(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param, RCPR_SYM(fiber)** resume_fib,
    const rcpr_uuid** restore_disc_id, int *resume_event, void** resume_param);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
