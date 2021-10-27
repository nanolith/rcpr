/**
 * \file models/shadow/resource/mock_resource_create.c
 *
 * \brief Check whether a resource instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/resource.h>

#include "../../../src/resource/resource_internal.h"

status mock_resource_release(RCPR_SYM(resource)* r);

/**
 * \brief Create a mock resource.
 *
 * \param r             Pointer to receive the mock resource.
 *
 * \returns a status code indicating success or failure.
 */
status mock_resource_create(RCPR_SYM(resource)** r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != r);

    *r = (RCPR_SYM(resource)*)malloc(sizeof(RCPR_SYM(resource)));
    if (NULL == *r)
    {
        return ERROR_GENERAL_OUT_OF_MEMORY;
    }

    RCPR_SYM(resource_init)(*r, &mock_resource_release);

    return STATUS_SUCCESS;
}
