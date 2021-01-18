/**
 * \file bigint/bigint_release.c
 *
 * \brief Release a \ref bigint instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>

#include "bigint_internal.h"

/**
 * \brief Release a \ref bigint instance.
 *
 * \param r             The \ref bigint \ref resource to release.
 *
 * \returns a status code indicating success or failure.
 */
status bigint_release(resource* r)
{
    status retval, reclaim_retval;
    bigint* i = (bigint*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_bigint_valid(i));

    /* clear the integer array. */
    memset(i->array, 0, i->length * sizeof(native_int));

    /* reclaim the array memory. */
    reclaim_retval = allocator_reclaim(i->a, i->array);

    /* reclaim the bigint memory. */
    retval = allocator_reclaim(i->a, i);

    /* if either failed, bubble up the failure code. */
    if (STATUS_SUCCESS == retval)
        retval = reclaim_retval;

    return retval;
}
