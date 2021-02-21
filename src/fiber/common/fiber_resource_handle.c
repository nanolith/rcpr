/**
 * \file fiber/common/fiber_resource_handle.c
 *
 * \brief Get the resource handle for a fiber.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "fiber_internal.h"

/**
 * \brief Given a \ref fiber instance, return the resource handle for this
 * \ref fiber instance.
 *
 * \param fib           The \ref fiber instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref fiber instance.
 */
resource* fiber_resource_handle(fiber* fib)
{
    MODEL_ASSERT(prop_fiber_valid(fib));

    return &(fib->hdr);
}
