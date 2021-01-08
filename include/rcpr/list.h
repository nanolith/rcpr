/**
 * \file rcpr/list.h
 *
 * \brief Double-linked list.
 *
 * The double-linked list is a simple container that holds a number of resources
 * stored in a linear fashion and provides both forward and reverse iteration.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/function_decl.h>
#include <rcpr/resource.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The list container holds zero or more resources in a linear fashion.
 */
typedef struct list list;

/**
 * \brief The list_node is a single node in an list container.
 */
typedef struct list_node list_node;

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref list instance.
 *
 * \param l             Pointer to the \ref list pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      list resource and to allocate new nodes.
 *
 * \note This \ref list is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref list_resource_handle on this \ref list instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p l must not reference a valid list instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p l is set to a pointer to a valid \ref list
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p l is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_create(
    list** l, allocator* a);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref list instance, return the resource handle for this
 * \ref list instance.
 *
 * \param l             The \ref list instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref list instance.
 */
resource* list_resource_handle(list* l);

/**
 * \brief Given a \ref list_node instance, return the resource handle for this
 * \ref list_node instance.
 *
 * \param node          The \ref list_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref list_node instance.
 */
resource* list_node_resource_handle(list_node* node);

/**
 * \brief Get the head of a \ref list.
 *
 * \param node          Pointer to the \ref list_node pointer to receive this
 *                      resource on success.
 * \param l             Pointer to the \ref list under query.
 *
 * \note This \ref list_node is owned by the \ref list queried.  To take
 * ownership of this \ref list_node, the caller must call \ref list_remove to
 * remove this \ref list_node from the \ref list.  However, it is possible to
 * change the \ref resource owned by this \ref list_node without first removing
 * it from the \ref list by calling \ref list_node_child_swap.
 *
 * If there is a head node, it is populated in \p node.  However, if this list
 * is empty, then \p node is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p node must not reference a valid \ref list_node instance and must
 *        not be NULL.
 *      - \p l must reference a valid \ref list and must not be NULL.
 *
 * \post
 *      - On success, \p node is set to the head of the \ref list, which can be
 *        NULL if \p l is empty.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_head(
    list_node** node, list* l);

/**
 * \brief Get the tail of a \ref list.
 *
 * \param node          Pointer to the \ref list_node pointer to receive this
 *                      resource on success.
 * \param l             Pointer to the \ref list under query.
 *
 * \note This \ref list_node is owned by the \ref list queried.  To take
 * ownership of this \ref list_node, the caller must call \ref list_remove to
 * remove this \ref list_node from the \ref list.  However, it is possible to
 * change the \ref resource owned by this \ref list_node without first removing
 * it from the \ref list by calling \ref list_node_child_swap.
 *
 * If there is a tail node, it is populated in \p node.  However, if this list
 * is empty, then \p node is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p node must not reference a valid \ref list_node instance and must
 *        not be NULL.
 *      - \p l must reference a valid \ref list and must not be NULL.
 *
 * \post
 *      - On success, \p node is set to the head of the \ref list, which can be
 *        NULL if \p l is empty.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_tail(
    list_node** node, list* l);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref list property.
 *
 * \param l              The \ref list instance to be verified.
 *
 * \returns true if the \ref list instance is valid.
 */
bool prop_list_valid(const list* l);

/**
 * \brief Valid \ref list_node property.
 *
 * \param node           The \ref list_node instance to be verified.
 *
 * \returns true if the \ref list_node instance is valid.
 */
bool prop_list_node_valid(const list_node* node);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
