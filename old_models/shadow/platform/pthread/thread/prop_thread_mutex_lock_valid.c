/**
 * \file models/shadow/platform/pthread/thread/prop_thread_mutex_lock_valid.c
 *
 * \brief Check whether a thread_mutex_lock instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../../../src/platform/pthread/thread/thread_internal.h"

RCPR_IMPORT_thread;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(thread_mutex_lock);

/**
 * \brief Valid \ref thread_mutex_lock property.
 *
 * \param lock          The \ref thread_mutex_lock instance to be verified.
 *
 * \returns true if the \ref thread_mutex_lock instance is valid.
 */
bool RCPR_SYM(prop_thread_mutex_lock_valid)(const thread_mutex_lock* lock)
{
    RCPR_MODEL_ASSERT(NULL != lock);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        lock->RCPR_MODEL_STRUCT_TAG_REF(thread_mutex_lock), thread_mutex_lock);

    return
        prop_thread_mutex_valid(lock->parent);
}
