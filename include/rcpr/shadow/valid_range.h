/**
 * \file rcpr/shadow/valid_range.h
 *
 * \brief Check memory access of the given pointer.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <stdbool.h>

bool prop_valid_range(void* arr, size_t size);
