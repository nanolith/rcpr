/**
 * \file auto_reset_trigger/auto_reset_trigger_register.c
 *
 * \brief Register a listener for this \ref auto_reset_trigger instance.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "auto_reset_trigger_internal.h"

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
    RCPR_SYM(auto_reset_trigger_callback) callback, void* context)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_auto_reset_trigger_valid(trigger));
    RCPR_MODEL_ASSERT(NULL != callback);

    /* We can only have one listener registered at a time. */
    if (NULL != trigger->callback)
    {
        return ERROR_AUTO_RESET_TRIGGER_LISTENER_ALREADY_REGISTERED;
    }

    /* register this listener. */
    trigger->callback = callback;
    trigger->context = context;

    return STATUS_SUCCESS;
}
