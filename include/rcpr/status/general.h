/**
 * \file rcpr/status/general.h
 *
 * \brief General status codes for RCPR.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Out-of-memory error.
 */
#define ERROR_GENERAL_OUT_OF_MEMORY \
    STATUS_CODE(1, RCPR_COMPONENT_GLOBAL, 0x0000)

/**
 * \brief A bad vtable was encountered.
 */
#define ERROR_GENERAL_BAD_VTABLE \
    STATUS_CODE(1, RCPR_COMPONENT_GLOBAL, 0x0001)
