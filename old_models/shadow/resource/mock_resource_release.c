/**
 * \file models/shadow/resource/mock_resource_release.c
 *
 * \brief Release a mock resource.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/resource.h>

/**
 * \brief Release a mock resource.
 *
 * \param r             Resource to release.
 *
 * \returns a status code indicating success or failure.
 */
status mock_resource_release(RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != r);

    free(r);

    return STATUS_SUCCESS;
}
