/**
 * \file auto_reset_trigger/auto_reset_trigger_signal.c
 *
 * \brief Signal the \ref auto_reset_trigger as a first step toward notifying
 * any listener.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "auto_reset_trigger_internal.h"

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
RCPR_SYM(auto_reset_trigger_signal)(RCPR_SYM(auto_reset_trigger)* trigger)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_auto_reset_trigger_valid(trigger));

    /* spring the trigger. */
    trigger->triggered = true;
}
