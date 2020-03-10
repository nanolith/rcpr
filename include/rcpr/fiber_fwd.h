/**
 * \file rcpr/fiber_fwd.h
 *
 * \brief Forward declarations for fiber library.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
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

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
