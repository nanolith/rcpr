/**
 * \file bigint/bigint_resource_handle.c
 *
 * \brief Get the resource handle for this bigint.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "bigint_internal.h"

/**
 * \brief Given a \ref bigint instance, return the resource handle for this
 * \ref bigint instance.
 *
 * \param i             The \ref bigint instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref bigint instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(bigint_resource_handle)(RCPR_SYM(bigint)* i)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_bigint_valid(i));

    /* return the resource handle for this bigint. */
    return &i->hdr;
}
