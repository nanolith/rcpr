/**
 * \file fiber/common/fiber_Scheduler_internal_discipline_id.c
 *
 * \brief The UUID for the internal fiber scheduler discipline.
 *
 * This discipline ID is used by default when a custom discipline ID is
 * unavailable.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

const rcpr_uuid FIBER_SCHEDULER_INTERNAL_DISCIPLINE = { .data = {
    0x50, 0x5a, 0xaf, 0x7d, 0x72, 0x01, 0x45, 0x2e,
    0x94, 0x9c, 0x46, 0xfa, 0x5a, 0x6f, 0x90, 0xde } };
