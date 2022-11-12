/**
 * \file rcpr/status/string.h
 *
 * \brief String status codes for RCPR.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Invalid parameter error.
 */
#define ERROR_STRING_INVALID_PARAMETER \
    STATUS_CODE(1, RCPR_COMPONENT_STRING, 0x0000)

/**
 * \brief An end-of-input condition was encountered when performing a string
 * iteration operation.
 */
#define ERROR_STRING_END_OF_INPUT \
    STATUS_CODE(1, RCPR_COMPONENT_STRING, 0x0001)
