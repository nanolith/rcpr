/**
 * \file auto_reset_trigger/auto_reset_trigger_internal.h
 *
 * \brief Internal functions and data structures for \ref auto_reset_trigger.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/auto_reset_trigger.h>
#include <rcpr/resource/protected.h>
#include <stdbool.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

struct RCPR_SYM(auto_reset_trigger)
{
    RCPR_SYM(resource) hdr;
    RCPR_SYM(allocator)* alloc;
    bool triggered;
    RCPR_SYM(auto_reset_trigger_callback) callback;
    void* context;
};

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
