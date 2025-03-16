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
 * \brief Begin a contract helper section.
 */
#define RCPR_BEGIN_CONTRACT_HELPER \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-parameter\"")

/**
 * \brief End a contract helper section.
 */
#define RCPR_END_CONTRACT_HELPER \
    _Pragma("GCC diagnostic pop")

/**
 * \brief Expansion of the begin preconditions variadic macro.
 */
#define RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN1(function, ...) \
    RCPR_BEGIN_CONTRACT_HELPER \
    inline void rcpr_model_check_ ## function ## _preconditions(__VA_ARGS__) {

/**
 * \brief Variadic macro describing function contract preconditions.
 */
#define RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(function, ...) \
    RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN1(function, __VA_ARGS__)

/**
 * \brief End of function contract preconditions.
 */
#define RCPR_MODEL_CONTRACT_PRECONDITIONS_END(function) \
    } \
    RCPR_END_CONTRACT_HELPER

/**
 * \brief Expansion of the begin postconditions variadic macro.
 */
#define RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN1(function, ...) \
    RCPR_BEGIN_CONTRACT_HELPER \
    inline void rcpr_model_check_ ## function ## _postconditions(__VA_ARGS__) {
