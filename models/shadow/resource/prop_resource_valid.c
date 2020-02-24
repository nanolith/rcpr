/**
 * \file models/shadow/resource/prop_resource_valid.c
 *
 * \brief Check whether a resource instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/resource/resource_internal.h"

/**
 * \brief Valid resource property.
 *
 * \param r             The resource instance to be verified.
 *
 * \returns true if the resource instance is valid.
 */
bool prop_resource_valid(const resource* r)
{
    return
           NULL != r
        && NULL != r->release;
}
