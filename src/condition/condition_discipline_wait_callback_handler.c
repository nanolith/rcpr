/**
 * \file condition/condition_discipline_wait_callback_handler.c
 *
 * \brief Handle a conditional wait request.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "condition_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_condition;
RCPR_IMPORT_condition_internal;
RCPR_IMPORT_rbtree;

/**
 * \brief The callback handler for a conditional wait request.
 *
 * \param context       Opaque pointer to the condition discipline context.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The yield event.
 * \param yield_param   Opaque pointer to the parameter for this yield.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_wait_callback_handler)(
    void* context, RCPR_SYM(fiber)* yield_fib, int yield_event,
    void* yield_param)
{
    (void)context;
    (void)yield_fib;
    (void)yield_event;
    (void)yield_param;

    return -1;
}
