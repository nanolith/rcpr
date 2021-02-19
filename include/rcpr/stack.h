/**
 * \file rcpr/stack.h
 *
 * \brief Stack allocation.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/allocator.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>

#pragma once

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The stack abstraction provides access to a stack that can be reclaimed
 * using resource_release on its resource handle.
 */
typedef struct stack stack;

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref stack of at least the given size.
 *
 * \param st            Pointer to the \ref stack pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      stack resource.
 * \param stack_size    The size of the stack in bytes.
 *
 * \note This \ref stack is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref stack_resource_handle on this \ref stack instance.  The stack must not
 * be in use by any \ref fiber or other process when it is released, or
 * undefined behavior can occur.  It is up to the caller to ensure that the
 * stack is not in use.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p st must not reference a valid \ref stack instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p stack_size must be greater than zero and must follow platform rules
 *        for creating a stack.
 *
 * \post
 *      - On success, \p stack is set to a pointer to a valid \ref stack
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p stack is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
stack_create(
    stack** st, allocator* a, size_t stack_size);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref stack instance, return the resource handle for this
 * \ref stack instance.
 *
 * \param st            The \ref stack instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref stack instance.
 */
resource* stack_resource_handle(stack* st);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref stack property.
 *
 * \param st             The \ref stack instance to be verified.
 *
 * \returns true if the \ref stack instance is valid.
 */
bool prop_stack_valid(const stack* st);

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
