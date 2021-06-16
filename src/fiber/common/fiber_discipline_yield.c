/**
 * \file fiber/common/fiber_discipline_yield.c
 *
 * \brief Yield to the fiber scheduler through a discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;

/**
 * \brief Yield to the fiber scheduler through the discipline.
 *
 * \param disc          The discipline.
 * \param yield_event   The discipline yield event.
 * \param yield_param   The yield event parameter.
 * \param resume_id     Pointer to receive the discipline resume id.
 * \param resume_event  Pointer to receive the discipline resume event.
 * \param resume_param  Pointer to receive the resume parameter.
 *
 * \note The currently executing fiber can call yield to yield to the scheduler
 * through the \ref fiber_scheduler_discipline.  The discipline yield event
 * describes the event causing the yield; this is translated to a unique yield
 * event in the scheduler.  The yield parameter can be used to send an optional
 * parameter to the scheduler.  When the fiber is resumed, the resume event
 * describes why it was resumed, and the resume parameter holds an optional
 * parameter for the resume.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p disc is a pointer to a valid \ref fiber_scheduler_discipline
 *        instance.
 *
 * \post
 *      - On success, the scheduler will suspend this fiber and start another.
 *        As far as the fiber is concerned, it will restart when the scheduler
 *        determines that it should restart, which will appear as a return from
 *        this function.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_discipline_yield)(
    RCPR_SYM(fiber_scheduler_discipline)* disc, int yield_event,
    void* yield_param, const rcpr_uuid** resume_id, int* resume_event,
    void** resume_param)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));
    MODEL_ASSERT(NULL != resume_id);
    MODEL_ASSERT(NULL != resume_event);
    MODEL_ASSERT(NULL != resume_param);

    /* convert the event to an offset. */
    size_t yield_offset = (size_t)yield_event;

    /* bounds checking. */
    if (yield_offset > disc->callback_vector_size)
    {
        return ERROR_FIBER_SCHEDULER_BAD_YIELD_EVENT;
    }

    /* look up the correct yield code based on the offset. */
    int decoded_yield_event = (int)disc->callback_codes[yield_offset];

    /* do the yield. */
    return
        fiber_scheduler_yield(
            disc->sched, decoded_yield_event, yield_param,
            resume_id, resume_event, resume_param);
}
