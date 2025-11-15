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
#include <rcpr/function_contracts.h>
#include <rcpr/function_decl.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/status.h>
#include <stdbool.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The list container holds zero or more resources in a linear fashion.
 */
typedef struct RCPR_SYM(list) RCPR_SYM(list);

/**
 * \brief The list_node is a single node in an list container.
 */
typedef struct RCPR_SYM(list_node) RCPR_SYM(list_node);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref list property.
 *
 * \param l             The \ref list instance to be verified.
 *
 * \returns true if the \ref list instance is valid.
 */
bool
RCPR_SYM(property_list_valid)(const RCPR_SYM(list)* l);

/**
 * \brief Valid \ref list_node property.
 *
 * \param node          The \ref list_node instance to be verified.
 *
 * \returns true if the \ref list_node instance is valid.
 */
bool
RCPR_SYM(property_list_node_valid)(const RCPR_SYM(list_node)* node);

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
RCPR_SYM(list_create)(
    RCPR_SYM(list)** l, RCPR_SYM(allocator)* a);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_create), RCPR_SYM(list)** l, RCPR_SYM(allocator)* a)
        /* l is a valid pointer. */
        RCPR_MODEL_CHECK_OBJECT_RW(l, sizeof(*l));
        /* a is a valid allocator. */
        RCPR_MODEL_ASSERT(property_allocator_valid(a));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_create))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_create), status retval, RCPR_SYM(list)** l,
    RCPR_SYM(allocator)* a)
        /* on success... */
        if (STATUS_SUCCESS == retval)
        {
            /* the list is valid. */
            RCPR_MODEL_ASSERT(property_list_valid(*l));
        }
        /* on failure. */
        else
        {
            /* the list pointer is set to NULL. */
            RCPR_MODEL_ASSERT(NULL == *l);

            /* the only error code returned is out-of-memory. */
            RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);
        }
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_create))

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
RCPR_SYM(list_insert_head)(
    RCPR_SYM(list)* l, RCPR_SYM(resource)* r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_insert_head), RCPR_SYM(list)* l, RCPR_SYM(resource)* r)
        /* l is a valid list. */
        RCPR_MODEL_ASSERT(property_list_valid(l));
        /* r is a valid resource. */
        RCPR_MODEL_ASSERT(prop_resource_valid(r));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_insert_head))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_insert_head), status retval, RCPR_SYM(list)* l,
    RCPR_SYM(resource)* r)
        /* l is a valid list. */
        RCPR_MODEL_ASSERT(property_list_valid(l));
        /* This method either succeeds or fails with
         * ERROR_GENERAL_OUT_OF_MEMORY. */
        RCPR_MODEL_ASSERT(
            (STATUS_SUCCESS == retval)
         || (ERROR_GENERAL_OUT_OF_MEMORY == retval));
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_insert_head))

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
RCPR_SYM(list_append_tail)(
    RCPR_SYM(list)* l, RCPR_SYM(resource)* r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_append_tail), RCPR_SYM(list)* l, RCPR_SYM(resource)* r)
        /* l is a valid list. */
        RCPR_MODEL_ASSERT(property_list_valid(l));
        /* r is a valid resource. */
        RCPR_MODEL_ASSERT(prop_resource_valid(r));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_append_tail))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_append_tail), status retval, RCPR_SYM(list)* l,
    RCPR_SYM(resource)* r)
        /* l is a valid list. */
        RCPR_MODEL_ASSERT(property_list_valid(l));
        /* This method either succeeds or fails with
         * ERROR_GENERAL_OUT_OF_MEMORY. */
        RCPR_MODEL_ASSERT(
            (STATUS_SUCCESS == retval)
         || (ERROR_GENERAL_OUT_OF_MEMORY == retval));
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_append_tail))

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
RCPR_SYM(list_append)(
    RCPR_SYM(list_node)* node, RCPR_SYM(resource)* r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_append), RCPR_SYM(list_node)* node, RCPR_SYM(resource)* r)
        /* node is a valid list node. */
        RCPR_MODEL_ASSERT(property_list_node_valid(node));
        /* r is a valid resource. */
        RCPR_MODEL_ASSERT(prop_resource_valid(r));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_append))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_append), status retval, RCPR_SYM(list_node)* node,
    RCPR_SYM(resource)* r)
        /* node is a valid list node. */
        RCPR_MODEL_ASSERT(property_list_node_valid(node));
        /* This method either succeeds or fails with
         * ERROR_GENERAL_OUT_OF_MEMORY. */
        RCPR_MODEL_ASSERT(
            (STATUS_SUCCESS == retval)
         || (ERROR_GENERAL_OUT_OF_MEMORY == retval));
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_append))

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
RCPR_SYM(list_insert)(
    RCPR_SYM(list_node)* node, RCPR_SYM(resource)* r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_insert), RCPR_SYM(list_node)* node, RCPR_SYM(resource)* r)
        /* node is a valid list node. */
        RCPR_MODEL_ASSERT(property_list_node_valid(node));
        /* r is a valid resource. */
        RCPR_MODEL_ASSERT(prop_resource_valid(r));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_insert))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_insert), status retval, RCPR_SYM(list_node)* node,
    RCPR_SYM(resource)* r)
        /* node is a valid list node. */
        RCPR_MODEL_ASSERT(property_list_node_valid(node));
        /* This method either succeeds or fails with
         * ERROR_GENERAL_OUT_OF_MEMORY. */
        RCPR_MODEL_ASSERT(
            (STATUS_SUCCESS == retval)
         || (ERROR_GENERAL_OUT_OF_MEMORY == retval));
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_insert))

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
RCPR_SYM(list_node_child_swap)(
    RCPR_SYM(list_node)* node, RCPR_SYM(resource)** r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_node_child_swap), RCPR_SYM(list_node)* node,
    RCPR_SYM(resource)** r)
        /* node is a valid list node. */
        RCPR_MODEL_ASSERT(property_list_node_valid(node));
        /* r is a valid pointer. */
        RCPR_MODEL_CHECK_OBJECT_RW(r, sizeof(*r));
        /* if *r is not NULL... */
        if (NULL != *r)
        {
            /* *r is a valid resource. */
            RCPR_MODEL_ASSERT(prop_resource_valid(*r));
        }
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_node_child_swap))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_node_child_swap), status retval, RCPR_SYM(list_node)* node,
    RCPR_SYM(resource)** r)
        /* this method always succeeds. TODO - make it return void. */
        RCPR_MODEL_ASSERT(STATUS_SUCCESS == retval);
        /* node is a valid list node. */
        RCPR_MODEL_ASSERT(property_list_node_valid(node));
        /* if *r is not NULL... */
        if (NULL != *r)
        {
            /* *r is a valid resource. */
            RCPR_MODEL_ASSERT(prop_resource_valid(*r));
        }
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_node_child_swap))

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
RCPR_SYM(list_pop)(
    RCPR_SYM(list)* l, RCPR_SYM(resource)** r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(list_pop), RCPR_SYM(list)* l, RCPR_SYM(resource)** r)
        /* l is a valid list. */
        RCPR_MODEL_ASSERT(property_list_valid(l));
        /* r is a valid pointer. */
        RCPR_MODEL_CHECK_OBJECT_RW(r, sizeof(*r));
        /* *r is NULL. */
        RCPR_MODEL_ASSERT(NULL == *r);
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(list_pop))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(list_pop), status retval, RCPR_SYM(list)* l,
    RCPR_SYM(resource)** r)
        /* l is a valid list. */
        RCPR_MODEL_ASSERT(property_list_valid(l));
        /* on success... */
        if (STATUS_SUCCESS == retval)
        {
            /* if *r is not NULL... */
            if (NULL != *r)
            {
                /* *r is a valid resource. */
                RCPR_MODEL_ASSERT(prop_resource_valid(*r));
            }
        }
        else
        {
            /* *r must be NULL. */
            RCPR_MODEL_ASSERT(NULL == *r);
        }
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(list_pop))

/**
 * \brief Swap the contents of two list instances.
 *
 * \param left          The left list instance for the swap.
 * \param right         The right list instance for the swap.
 *
 * \note This operation always succeeds, as long as \p left and \p right are
 * valid. If either are invalid, the result of this operation is unpredictable
 * and will likely crash.
 *
 * \pre
 *      - \p left must point to a valid \ref list instance.
 *      - \p right must point to a valid \ref list instance.
 * \post
 *      - \p left contains and owns the contents previously contained and owned
 *      by \p right.
 *      - \p right contains and owns the contents previously contained and owned
 *      by \p left.
 */
void RCPR_SYM(list_swap)(RCPR_SYM(list)* left, RCPR_SYM(list)* right);

/**
 * \brief Clear a list instance, removing all nodes and their resources.
 *
 * \param l             The list to clear.
 *
 * \pre
 *      - \p l must point to a valid \ref list instance.
 * \post
 *      - On success, \p l points to a valid \ref slist instance that has zero
 *        nodes.
 *      - On failure, \p l may still contain some nodes.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_clear)(RCPR_SYM(list)* l);

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
RCPR_SYM(resource)*
RCPR_SYM(list_resource_handle)(
    RCPR_SYM(list)* l);

/**
 * \brief Given a \ref list_node instance, return the resource handle for this
 * \ref list_node instance.
 *
 * \param node          The \ref list_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref list_node instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(list_node_resource_handle)(
    RCPR_SYM(list_node)* node);

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
RCPR_SYM(list_head)(
    RCPR_SYM(list_node)** node, RCPR_SYM(list)* l);

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
RCPR_SYM(list_tail)(
    RCPR_SYM(list_node)** node, RCPR_SYM(list)* l);

/**
 * \brief Get the count of nodes in a \ref list.
 *
 * \param l             Pointer to the \ref list under query.
 *
 * \returns the number of nodes in the given \ref list.
 */
size_t RCPR_SYM(list_count)(RCPR_SYM(list)* l);

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
RCPR_SYM(list_node_child)(
    RCPR_SYM(resource)** r, RCPR_SYM(list_node)* node);

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
RCPR_SYM(list_node_next)(
    RCPR_SYM(list_node)** next, RCPR_SYM(list_node)* node);

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
RCPR_SYM(list_node_prev)(
    RCPR_SYM(list_node)** prev, RCPR_SYM(list_node)* node);

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
bool RCPR_SYM(prop_list_valid)(const RCPR_SYM(list)* l);

/**
 * \brief Valid \ref list_node property.
 *
 * \param node           The \ref list_node instance to be verified.
 *
 * \returns true if the \ref list_node instance is valid.
 */
bool RCPR_SYM(prop_list_node_valid)(const RCPR_SYM(list_node)* node);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_list_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(list) sym ## list; \
    typedef RCPR_SYM(list_node) sym ## list_node; \
    static inline status FN_DECL_MUST_CHECK sym ## list_create( \
        RCPR_SYM(list)** x, RCPR_SYM(allocator)* y) { \
            return RCPR_SYM(list_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_insert_head( \
        RCPR_SYM(list)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(list_insert_head)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_append_tail( \
        RCPR_SYM(list)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(list_append_tail)(x, y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_append( \
        RCPR_SYM(list_node)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(list_append)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_insert( \
        RCPR_SYM(list_node)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(list_insert)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_node_child_swap( \
        RCPR_SYM(list_node)* x, RCPR_SYM(resource)** y) { \
            return RCPR_SYM(list_node_child_swap)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_pop( \
        RCPR_SYM(list)* x, RCPR_SYM(resource)** y) { \
            return RCPR_SYM(list_pop)(x,y); } \
    static inline void sym ## list_swap( \
        RCPR_SYM(list)* x, RCPR_SYM(list)* y) { \
            RCPR_SYM(list_swap)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_clear( \
        RCPR_SYM(list)* x) { \
            return RCPR_SYM(list_clear)(x); } \
    static inline RCPR_SYM(resource)* sym ## list_resource_handle( \
        RCPR_SYM(list)* x) { \
            return RCPR_SYM(list_resource_handle)(x); } \
    static inline RCPR_SYM(resource)* sym ## list_node_resource_handle( \
        RCPR_SYM(list_node)* x) { \
            return RCPR_SYM(list_node_resource_handle)(x); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_head( \
        RCPR_SYM(list_node)** x, RCPR_SYM(list)* y) { \
            return RCPR_SYM(list_head)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_tail( \
        RCPR_SYM(list_node)** x, RCPR_SYM(list)* y) { \
            return RCPR_SYM(list_tail)(x,y); } \
    static inline size_t sym ## list_count( \
        RCPR_SYM(list)* x) { \
            return  RCPR_SYM(list_count)(x); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_node_child( \
        RCPR_SYM(resource)** x, RCPR_SYM(list_node)* y) { \
            return RCPR_SYM(list_node_child)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_node_next( \
        RCPR_SYM(list_node)** x, RCPR_SYM(list_node)* y) { \
            return RCPR_SYM(list_node_next)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## list_node_prev( \
        RCPR_SYM(list_node)** x, RCPR_SYM(list_node)* y) { \
            return RCPR_SYM(list_node_prev)(x,y); } \
    static inline bool sym ## prop_list_valid( \
        const RCPR_SYM(list)* x) { \
            return RCPR_SYM(prop_list_valid)(x); } \
    static inline bool sym ## prop_list_node_valid( \
        const RCPR_SYM(list_node)* x) { \
            return RCPR_SYM(prop_list_node_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_list_as(sym) \
    __INTERNAL_RCPR_IMPORT_list_sym(sym ## _)
#define RCPR_IMPORT_list \
    __INTERNAL_RCPR_IMPORT_list_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
