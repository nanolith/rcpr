/**
 * \file select/psock_idle_fiber_entry.c
 *
 * \brief Entry point for the idle fiber for psock I/O.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber/disciplines/psock_io.h>
#include <rcpr/model_assert.h>
#include <sys/types.h>
#include <sys/event.h>

#include "../../psock_internal.h"

/**
 * \brief The entry point for the psock idle fiber.
 *
 * This idle fiber handles the platform-specific event loop for I/O events, and
 * will sleep until a descriptor is available for a requested read or write.
 *
 * \param context       The user context for this fiber.
 *
 * \returns a status code indicating success or failure when this fiber
 * terminates.
 */
status psock_idle_fiber_entry(void* context)
{
    /* TODO - fill out stub. */
    (void)context;

    return -1;
}
