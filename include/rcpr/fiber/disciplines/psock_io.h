/**
 * \file rcpr/fiber/disciplines/psock_io.h
 *
 * \brief The RCPR psock I/O fiber scheduler discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/fiber.h>
#include <rcpr/uuid.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The psock I/O fiber scheduler discipline.
 */
extern const rcpr_uuid FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE;

/**
 * \brief psock I/O discipline yield events.
 */
enum fiber_scheduler_psock_io_discipline_yield_events
{
    /** \brief Wait on a read I/O event. */
    FIBER_SCHEDULER_PSOCK_IO_YIELD_EVENT_WAIT_READ                  = 0x0000,
    /** \brief Wait on a write I/O event. */
    FIBER_SCHEDULER_PSOCK_IO_YIELD_EVENT_WAIT_WRITE                 = 0x0001,
};

/**
 * \brief The psock I/O discipline resume events.
 */
enum fiber_scheduler_psock_io_discipline_resume_events
{
    /** \brief This event occurs when a descriptor is available for read. */
    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_READ            = 0x0000,

    /** \brief This event occurs when a descriptor is available for write. */
    FIBER_SCHEDULER_PSOCK_IO_RESUME_EVENT_AVAILABLE_WRITE           = 0x0001,
};

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
