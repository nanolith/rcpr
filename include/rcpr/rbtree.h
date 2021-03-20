/**
 * \file rcpr/rbtree.h
 *
 * \brief The RCPR red/black tree library.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/compare.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief An rbtree stores resources in a balanced binary tree.
 */
typedef struct rbtree rbtree;

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create an \ref rbtree instance.
 *
 * \param tree          Pointer to the \ref rbtree pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      rbtree resource.
 * \param compare       The \ref compare_fn to use to compare two resources in
 *                      this \ref rbtree instance.
 * \param context       Pointer to the context to pass to the comparison
 *                      function.
 *
 * \note This \ref rbtree is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref rbtree_resource_handle on this \ref rbtree instance.
 *
 * Any resource added to this \ref rbtree via \ref rbtree_insert is owned by the
 * \ref rbtree and will be released when the \ref rbtree resource handle is
 * released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p tree must not reference a valid \ref tree instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p compare must reference a valid \ref compare_fn function.
 *
 * \post
 *      - On success, \p tree is set to a pointer to a valid \ref rbtree
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p tree is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
rbtree_create(rbtree** tree, allocator* a, compare_fn compare, void* context);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref rbtree instance, return the resource handle for this
 * \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree instance.
 */
resource* rbtree_resource_handle(rbtree* tree);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref rbtree property.
 *
 * \param tree          The \ref rbtree instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool prop_rbtree_valid(const rbtree* tree);

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
