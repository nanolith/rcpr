/**
 * \file auto_reset_trigger/auto_reset_trigger_step.c
 *
 * \brief Step the \ref auto_reset_trigger instance, which may result in the
 * listener being called.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "auto_reset_trigger_internal.h"

/**
 * \brief Step an \ref auto_reset_trigger, potentially calling the registered
 * listener and resetting.
 *
 * \param trigger       The \ref auto_reset_trigger instance for this operation.
 */
void
RCPR_SYM(auto_reset_trigger_step)(RCPR_SYM(auto_reset_trigger)* trigger)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_auto_reset_trigger_valid(trigger));

    /* Has the trigger been signaled? */
    if (trigger->triggered)
    {
        /* Is there a listener? */
        if (NULL != trigger->callback)
        {
            /* notify the listener. */
            (trigger->callback)(trigger->context);

            /* reset the trigger. */
            trigger->triggered = false;
            trigger->callback = NULL;
            trigger->context = NULL;
        }
    }
}
