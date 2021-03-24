/**
 * \file rcpr/status/rbtree.h
 *
 * \brief rbtree status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief A NIL node resource cannot be released.
 */
#define ERROR_RBTREE_NIL_NODE_CANNOT_BE_RELEASED \
    STATUS_CODE(1, RCPR_COMPONENT_RBTREE, 0x0000)
