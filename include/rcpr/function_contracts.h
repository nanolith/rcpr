/**
 * \file rcpr/function_contracts.h
 *
 * \brief Function contract macros for handling preconditions, postconditions,
 * and model checks.
 *
 * \copyright 2024 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

/**
 * Begin a contract helper section.
 */
#define RCPR_BEGIN_CONTRACT_HELPER \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-parameter\"")

/**
 * End a contract helper section.
 */
#define RCPR_END_CONTRACT_HELPER \
    _Pragma("GCC diagnostic pop")
