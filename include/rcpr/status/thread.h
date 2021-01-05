/**
 * \file rcpr/status/thread.h
 *
 * \brief Thread status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Thread attribute initialization error.
 */
#define ERROR_THREAD_ATTRIBUTE_INIT \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0000)

/**
 * \brief Thread attribute stack size error.
 */
#define ERROR_THREAD_ATTRIBUTE_SETSTACKSIZE \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0001)

/**
 * \brief Thread create error.
 */
#define ERROR_THREAD_CREATE \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0002)

/**
 * \brief Thread join error.
 */
#define ERROR_THREAD_JOIN \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0003)

/**
 * \brief Mutex init error.
 */
#define ERROR_THREAD_MUTEX_INIT \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0004)

/**
 * \brief Mutex destroy error.
 */
#define ERROR_THREAD_MUTEX_DESTROY \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0005)

/**
 * \brief Mutex unlock error.
 */
#define ERROR_THREAD_MUTEX_UNLOCK \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0006)

/**
 * \brief Mutex lock error.
 */
#define ERROR_THREAD_MUTEX_LOCK \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0007)

/**
 * \brief Condition variable init error.
 */
#define ERROR_THREAD_COND_INIT \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0008)

/**
 * \brief Condition variable destroy error.
 */
#define ERROR_THREAD_COND_DESTROY \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0009)
