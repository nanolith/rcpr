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

#include <rcpr/allocator.h>
#include <rcpr/function_decl.h>
#include <rcpr/resource.h>

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
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create an \ref auto_reset_trigger that can accommodate a single
 * listener.
 *
 * An \ref auto_reset_trigger will notify its listener when signaled. After the
 * listener is notified, it is removed, and the trigger is reset. After
 * notification, the listener must register with the trigger again to receive a
 * future notification. If there is no registered listener when the trigger is
 * signaled, then it will remain in signaled mode until a listener registers, at
 * which point, it will receive the notification and the trigger will be reset.
 *
 * Notifications occur when the trigger is stepped. This two step process allows
 * any side-effects that must occur after registration to be ordered prior to
 * the notification occurring. One could imagine, for instance, that the
 * registration process writes a status to a client socket as does the
 * notification process. If notification happened immediately after
 * registration, this ordering would be broken. So, the correct ordering of
 * events would be to signal the trigger, then step it, or to register the
 * trigger, then step it. Between signal and step or register and step, there is
 * an opportunity for the caller to perform operations requiring strict
 * ordering.
 *
 * \param trigger       Pointer to the \ref auto_reset_trigger pointer to be set
 *                      to this instance on success.
 * \param alloc         The allocator to use for this operation.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(auto_reset_trigger_create)(
    RCPR_SYM(auto_reset_trigger)** trigger, RCPR_SYM(allocator)* alloc);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Signal an \ref auto_reset_trigger, placing it into the triggered
 * state.
 *
 * \param trigger       The \ref auto_reset_trigger instance for this operation.
 */
void
RCPR_SYM(auto_reset_trigger_signal)(RCPR_SYM(auto_reset_trigger)* trigger);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref auto_reset_trigger instance, return the resource handle
 * for this \ref auto_reset_trigger instance.
 *
 * \param trigger           The \ref auto_reset_trigger from which this resource
 *                          handle is returned.
 *
 * \returns the resource handle for this \ref auto_reset_trigger instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(auto_reset_trigger_resource_handle)(
    RCPR_SYM(auto_reset_trigger)* trigger);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_auto_reset_trigger_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(auto_reset_trigger) sym ## auto_reset_trigger; \
    typedef RCPR_SYM(auto_reset_trigger_callback) \
    sym ## auto_reset_trigger_callback; \
    static inline status FN_DECL_MUST_CHECK sym ## auto_reset_trigger_create( \
        RCPR_SYM(auto_reset_trigger)** x, RCPR_SYM(allocator)* y) { \
            return RCPR_SYM(auto_reset_trigger_create)(x,y); } \
    static inline RCPR_SYM(resource)* \
    sym ## auto_reset_trigger_resource_handle( \
        RCPR_SYM(auto_reset_trigger)* x) { \
            return RCPR_SYM(auto_reset_trigger_resource_handle)(x); } \
    static inline void sym ## auto_reset_trigger_signal( \
        RCPR_SYM(auto_reset_trigger)* x) { \
            return RCPR_SYM(auto_reset_trigger_signal)(x); } \
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
