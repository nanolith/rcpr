/**
 * \file rcpr/auto_reset_trigger.h
 *
 * \brief An auto-reset trigger is a one-shot trigger that resets on
 * (potentially delayed) notification.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The auto-reset trigger.
 */
typedef struct RCPR_SYM(auto_reset_trigger) RCPR_SYM(auto_reset_trigger);

/**
 * \brief An auto-reset trigger notification callback.
 */
typedef void (*RCPR_SYM(auto_reset_trigger_callback))(void*);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_auto_reset_trigger_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(auto_reset_trigger) sym ## auto_reset_trigger; \
    typedef RCPR_SYM(auto_reset_trigger_callback) \
    sym ## auto_reset_trigger_callback; \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_auto_reset_trigger_as(sym) \
    __INTERNAL_RCPR_IMPORT_auto_reset_trigger_sym(sym ## _)
#define RCPR_IMPORT_auto_reset_trigger \
    __INTERNAL_RCPR_IMPORT_auto_reset_trigger_sym()

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
