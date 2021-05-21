/**
 * \file kqueue/psock_fiber_scheduler_discipline_set_resource_release.c
 *
 * \brief Set the resource release override for this discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../psock_internal.h"

/**
 * \brief Hook the fiber discipline resource release method in order to ensure
 * that the psock fiber discipline context resource is release as part of the
 * release of this fiber discipline resource.
 * 
 * \param disc          The discipline to override.
 */
void psock_fiber_scheduler_discipline_set_resource_release(
    fiber_scheduler_discipline* disc)
{
    /* TODO - fill out stub. */
    (void)disc;
}
