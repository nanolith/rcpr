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

/**
 * \brief Insert the given \ref resource in the front of the \ref list.
 *
 * \param l             Pointer to the \ref list for the insert operation.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the head of the list.  The
 * \ref list takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p l must be a valid \ref list instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted to the head of \p l.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
list_insert_head(
    list* l, resource* r);

/**
 * \brief Append the given \ref resource to the back of the \ref list.
 *
 * \param l             Pointer to the \ref list for the append operation.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the tail of the list.  The
 * \ref list takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p l must be a valid \ref list instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended to the end of \p l.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
list_append_tail(
    list* l, resource* r);

/**
 * \brief Append the given \ref resource to the next value of the given \ref
 * list_node.
 *
 * If there is already a next node, then this \ref resource is placed between
 * the given \ref list_node and its next node.
 *
 * \param node          Pointer to the \ref list_node to which the
 *                      \ref resource should be appended.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the next node of the provided
 * \ref list_node. The parent \ref list takes ownership of the \ref resource
 * pointed to by \p r and will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must be a valid \ref list_node assigned to a \ref list
 *        instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended after \p node in the \ref list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
list_append(
    list_node* node, resource* r);

/**
 * \brief Insert the given \ref resource before the given \ref list_node.
 *
 * If there is already a previous node, then this \ref resource is placed
 * between the given \ref list_node and its previous node.
 *
 * \param node          Pointer to the \ref list_node to which the
 *                      \ref resource should be inserted.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a \ref list_node will be created to hold the
 * given \ref resource, and this node will become the prev node of the provided
 * \ref list_node. The parent \ref list takes ownership of the \ref resource
 * pointed to by \p r and will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must be a valid \ref list_node assigned to a \ref list
 *        instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted before \p node in the \ref list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
list_insert(
    list_node* node, resource* r);

/**
 * \brief Swap the \ref resource owned by this \ref list_node with the given
 * resource, replacing it with the value currently owned by this node.
 *
 * \param node          Pointer to the \ref list_node to modify.
 * \param r             Pointer to the \ref resource pointer to be swapped.
 *
 * \note This operation swaps the ownership of a child resource associated with
 * the \ref list_node \p node.  If the value pointed to by \p r is NULL, then
 * the caller takes ownership of the child and the \p node no longer has a child
 * associated with it.  If the value pointed to by \p r is not NULL, then it
 * must be a valid \ref resource, and \p node takes ownership of this \ref
 * resource. If \p node is owned by a \ref list instance, then the lifetime of
 * this \ref resource is tied to the lifetime of the \ref list instance.  If \p
 * node is not owned by a \ref list instance, then it is the responsibility of
 * the caller to release \p node.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - either \p r must be NULL, or must reference a valid \ref resource
 *        instance.
 *      - \p node must reference a valid \ref list_node and must not be NULL.
 *
 * \post
 *      - On success, \p r is set to the child resource owned by \p node, and \p
 *        node takes ownership of the \ref resource previously pointed to by \p
 *        r.
 *      - On failure, \p r is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_node_child_swap(
    list_node* node, resource** r);

/**
 * \brief Pop the head value of the list, setting the given resource pointer to
 * the resource previously held in the head node.
 *
 * The next node in the list after head becomes the new head node.
 *
 * \param l             Pointer to the \ref list instance to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      head value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * \ref list_node.  This \ref list_node is released; the caller assumes
 * ownership of the \ref resource and must release it when it is no longer
 * needed.  If the \ref resource pointer is NULL, then there was either no
 * resource associated with that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p l must reference a valid \ref list and must not be NULL.
 *
 * \post
 *      - On success, if \p l has a at least one node, then
 *          - if the head node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the head node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the head node is released, and the next node becomes the head
 *            node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
list_pop(
    list* l, resource** r);

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

/**
 * \brief Get the count of nodes in a \ref list.
 *
 * \param l             Pointer to the \ref list under query.
 *
 * \returns the number of nodes in the given \ref list.
 */
size_t list_count(list* l);

/**
 * \brief Get the resource associated with the given of \ref list_node.
 *
 * \param r             Pointer to the \ref resource pointer to receive this
 *                      child resource.
 * \param node          Pointer to the \ref list_node under query.
 *
 * \note This \ref resource is owned by the \ref list_node queried.  To take
 * ownership of this \ref resource, the caller must call \ref
 * list_node_child_swap to remove this \ref resource from the \ref list_node.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must not reference a valid \ref resource instance and must be
 *        NULL.
 *      - \p node must reference a valid \ref list_node and must not be NULL.
 *
 * \post
 *      - On success, \p r is set to the child resource owned by \p node.
 *      - On failure, \p r is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_node_child(
    resource** r, list_node* node);

/**
 * \brief Given an \ref list_node, return the next \ref list_node in the list.
 *
 * \param next          Pointer to the \ref list_node pointer to receive the
 *                      next value.
 * \param node          Pointer to the \ref list_node under query.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p next must not reference a valid \ref list_node instance and must
 *        be NULL.
 *      - \p node must reference a valid \ref list_node and must not be NULL.
 *
 * \post
 *      - On success, \p next is set to the next node in this list, or NULL if
 *        \p node is the tail of the list.
 *      - On failure, \p next is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_node_next(
    list_node** next, list_node* node);

/**
 * \brief Given an \ref list_node, return the previous \ref list_node in the
 * list.
 *
 * \param prev          Pointer to the \ref list_node pointer to receive the
 *                      prev value.
 * \param node          Pointer to the \ref list_node under query.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p prev must not reference a valid \ref list_node instance and must
 *        be NULL.
 *      - \p node must reference a valid \ref list_node and must not be NULL.
 *
 * \post
 *      - On success, \p prev is set to the previous node in this list, or NULL
 *      if \p node is the head of the list.
 *      - On failure, \p prev is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_node_prev(
    list_node** prev, list_node* node);

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
