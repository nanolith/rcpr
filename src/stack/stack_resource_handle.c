/**
 * \file stack/stack_resource_handle.c
 *
 * \brief Get the resource handle for a stack.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "stack_internal.h"

/**
 * \brief Given a \ref stack instance, return the resource handle for this
 * \ref stack instance.
 *
 * \param st            The \ref stack instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref stack instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(stack_resource_handle)(
    RCPR_SYM(stack)* st)
{
    MODEL_ASSERT(prop_stack_valid(st));

    return &(st->hdr);
}
