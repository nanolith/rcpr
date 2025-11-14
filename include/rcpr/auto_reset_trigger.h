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
#include <rcpr/function_contracts.h>
#include <rcpr/function_decl.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/status.h>
#include <stdbool.h>

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
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid allocator property.
 *
 * \param trigger       The \ref auto_reset_trigger instance to be verified.
 *
 * \returns true if the \ref auto_reset_trigger instance is valid.
 */
bool
RCPR_SYM(property_auto_reset_trigger_valid)(
    const RCPR_SYM(auto_reset_trigger)* trigger);

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

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_create),
    RCPR_SYM(auto_reset_trigger)** trigger, RCPR_SYM(allocator)* alloc)
        /* trigger is a valid pointer. */
        RCPR_MODEL_CHECK_OBJECT_RW(trigger, sizeof(*trigger));
        /* alloc is a valid allocator. */
        RCPR_MODEL_ASSERT(property_allocator_valid(alloc));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(auto_reset_trigger_create))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_create),
    int retval, RCPR_SYM(auto_reset_trigger)** trigger,
    RCPR_SYM(allocator)* alloc)
        /* on success... */
        if (STATUS_SUCCESS == retval)
        {
            /* the trigger is valid. */
            RCPR_MODEL_ASSERT(property_auto_reset_trigger_valid(*trigger));
        }
        /* on failure. */
        else
        {
            /* the trigger pointer is set to NULL. */
            RCPR_MODEL_ASSERT(NULL == *trigger);

            /* the only error code returned is out-of-memory. */
            RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);
        }
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(auto_reset_trigger_create))

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Signal an \ref auto_reset_trigger, placing it into the triggered
 * state.
 *
 * This is the first step in a two step process. The trigger should be signaled,
 * and the trigger should be stepped in order to complete the signaling process.
 * This ensures that the caller can perform any ordered step that must occur
 * between the signaling and when the trigger executes the listener callback.
 *
 * \param trigger       The \ref auto_reset_trigger instance for this operation.
 */
void
RCPR_SYM(auto_reset_trigger_signal)(RCPR_SYM(auto_reset_trigger)* trigger);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_signal), RCPR_SYM(auto_reset_trigger)* trigger)
        /* trigger valid. */
        RCPR_MODEL_ASSERT(property_auto_reset_trigger_valid(trigger));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(auto_reset_trigger_signal))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_signal), RCPR_SYM(auto_reset_trigger)* trigger)
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(auto_reset_trigger_signal))

/**
 * \brief Step an \ref auto_reset_trigger, potentially calling the registered
 * listener and resetting.
 *
 * \param trigger       The \ref auto_reset_trigger instance for this operation.
 */
void
RCPR_SYM(auto_reset_trigger_step)(RCPR_SYM(auto_reset_trigger)* trigger);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_step), RCPR_SYM(auto_reset_trigger)* trigger)
        /* trigger valid. */
        RCPR_MODEL_ASSERT(property_auto_reset_trigger_valid(trigger));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(auto_reset_trigger_step))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_step), RCPR_SYM(auto_reset_trigger)* trigger)
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(auto_reset_trigger_step))

/**
 * \brief Register the listener for this \ref auto_reset_trigger instance.
 *
 * This is the first step in a two step process. The listener should be
 * registered, and the trigger should be stepped to see if it has already been
 * tripped.
 *
 * \param trigger       The \ref auto_reset_trigger instance for this operation.
 * \param callback      The listener callback method.
 * \param context       The user context pointer for this listener.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(auto_reset_trigger_register)(
    RCPR_SYM(auto_reset_trigger)* trigger,
    RCPR_SYM(auto_reset_trigger_callback) callback, void* context);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(auto_reset_trigger_register),
    RCPR_SYM(auto_reset_trigger)* trigger,
    RCPR_SYM(auto_reset_trigger_callback) callback, void* context)
        /* trigger valid. */
        RCPR_MODEL_ASSERT(property_auto_reset_trigger_valid(trigger));
        /* callback is not NULL. */
        RCPR_MODEL_ASSERT(NULL == callback);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(auto_reset_trigger_register))

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
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref auto_reset_trigger property.
 *
 * \param trigger       The \ref auto_reset_trigger instance to be verified.
 *
 * \returns true if the \ref auto_reset_trigger instance is valid.
 */
bool
RCPR_SYM(prop_auto_reset_trigger_valid)(
    const RCPR_SYM(auto_reset_trigger)* trigger);

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
            RCPR_SYM(auto_reset_trigger_signal)(x); } \
    static inline void sym ## auto_reset_trigger_step( \
        RCPR_SYM(auto_reset_trigger)* x) { \
            RCPR_SYM(auto_reset_trigger_step)(x); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## auto_reset_trigger_register( \
        RCPR_SYM(auto_reset_trigger)* x, \
        RCPR_SYM(auto_reset_trigger_callback) y, void* z) { \
            return RCPR_SYM(auto_reset_trigger_register)(x,y,z); } \
    static inline bool \
    sym ## prop_auto_reset_trigger_valid( \
        const RCPR_SYM(auto_reset_trigger)* x) { \
            return RCPR_SYM(prop_auto_reset_trigger_valid)(x); } \
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
