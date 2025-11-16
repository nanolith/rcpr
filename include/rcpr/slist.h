/**
 * \file rcpr/slist.h
 *
 * \brief Single-linked list.
 *
 * The single-linked list is a simple container that holds a number of resources
 * stored in a linear fashion.
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
 * \brief The slist container holds zero or more resources in a linear fashion.
 */
typedef struct RCPR_SYM(slist) RCPR_SYM(slist);

/**
 * \brief The slist_node is a single node in an slist container.
 */
typedef struct RCPR_SYM(slist_node) RCPR_SYM(slist_node);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref slist property.
 *
 * \param l             The \ref slist instance to be verified.
 *
 * \returns true if the \ref slist instance is valid.
 */
bool
RCPR_SYM(property_slist_valid)(const RCPR_SYM(slist)* l);

/**
 * \brief Valid \ref slist_node property.
 *
 * \param node          The \ref slist_node instance to be verified.
 *
 * \returns true if the \ref slist_node instance is valid.
 */
bool
RCPR_SYM(property_slist_node_valid)(const RCPR_SYM(slist_node)* node);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref slist instance.
 *
 * \param list          Pointer to the \ref slist pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      slist resource and to allocate new nodes.
 *
 * \note This \ref slist is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref slist_resource_handle on this \ref slist instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p list must not reference a valid list instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p list is set to a pointer to a valid \ref slist
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p list is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_create)(
    RCPR_SYM(slist)** list, RCPR_SYM(allocator)* a);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Insert the given \ref resource in the front of the \ref slist.
 *
 * \param list          Pointer to the \ref slist for the insert operation.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a \ref slist_node will be created to hold the
 * given \ref resource, and this node will become the head of the list.  The
 * \ref slist takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p list must be a valid \ref slist instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted to the head of \p list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_insert_head)(
    RCPR_SYM(slist)* list, RCPR_SYM(resource)* r);

/**
 * \brief Append the given \ref resource to the back of the \ref slist.
 *
 * \param list          Pointer to the \ref slist for the append operation.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref slist_node will be created to hold the
 * given \ref resource, and this node will become the tail of the list.  The
 * \ref slist takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p list must be a valid \ref slist instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended to the end of \p list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_append_tail)(
    RCPR_SYM(slist)* list, RCPR_SYM(resource)* r);

/**
 * \brief Append the given \ref resource to the next value of the given \ref
 * slist_node.
 *
 * If there is already a next node, then this \ref resource is placed between
 * the given \ref slist_node and its next node.
 *
 * \param node          Pointer to the \ref slist_node to which the
 *                      \ref resource should be appended.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a \ref slist_node will be created to hold the
 * given \ref resource, and this node will become the next node of the provided
 * \ref slist_node. The parent \ref slist takes ownership of the \ref resource
 * pointed to by \p r and will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must be a valid \ref slist_node assigned to a \ref slist
 *        instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended to the end of \p list.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_append)(
    RCPR_SYM(slist_node)* node, RCPR_SYM(resource)* r);

/**
 * \brief Swap the \ref resource owned by this \ref slist_node with the given
 * resource, replacing it with the value currently owned by this node.
 *
 * \param node          Pointer to the \ref slist_node to modify.
 * \param r             Pointer to the \ref resource pointer to be swapped.
 *
 * \note This operation swaps the ownership of a child resource associated with
 * the \ref slist_node \p node.  If the value pointed to by \p r is NULL, then
 * the caller takes ownership of the child and the \p node no longer has a child
 * associated with it.  If the value pointed to by \p r is not NULL, then it
 * must be a valid \ref resource, and \p node takes ownership of this \ref
 * resource. If \p node is owned by a \ref slist instance, then the lifetime of
 * this \ref resource is tied to the lifetime of the \ref slist instance.  If \p
 * node is not owned by a \ref slist instance, then it is the responsibility of
 * the caller to release \p node.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - either \p r must be NULL, or must reference a valid \ref resource
 *        instance.
 *      - \p node must reference a valid \ref slist_node and must not be NULL.
 *
 * \post
 *      - On success, \p r is set to the child resource owned by \p node, and \p
 *        node takes ownership of the \ref resource previously pointed to by \p
 *        r.
 *      - On failure, \p r is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_child_swap)(
    RCPR_SYM(slist_node)* node, RCPR_SYM(resource)** r);

/**
 * \brief Pop the head value of the list, setting the given resource pointer to
 * the resource previously held in the head node.
 *
 * The next node in the list after head becomes the new head node.
 *
 * \param list          Pointer to the \ref slist instance to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      head value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * \ref slist_node.  This \ref slist_node is released; the caller assumes
 * ownership of the \ref resource and must release it when it is no longer
 * needed.  If the \ref resource pointer is NULL, then there was either no
 * resource associated with that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p list must reference a valid \ref slist and must not be NULL.
 *
 * \post
 *      - On success, if \p list has a at least one node, then
 *          - if the head node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the head node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the head node is released, and the next node becomes the head
 *            node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_pop)(
    RCPR_SYM(slist)* list, RCPR_SYM(resource)** r);

/**
 * \brief Pop the next value of the given node, setting the given resource
 * pointer to the resource previously held by the next node.
 *
 * The next node in the list after node next becomes node next.
 *
 * \param node          Pointer to the \ref slist_node instance prior to the
 *                      node to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      next node value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * \ref slist_node.  This \ref slist_node is released; the caller assumes
 * ownership of the \ref resource and must release it when it is no longer
 * needed.  If the \ref resource pointer is NULL, then there was either no
 * resource associated with that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p node must reference a valid \ref slist_node and must not be NULL.
 *
 * \post
 *      - On success, if \p node has a at least one next node, then
 *          - if the next node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the next node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the next node is released, and the next next node becomes the next
 *            node for \p node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_next_pop)(
    RCPR_SYM(slist_node)* node, RCPR_SYM(resource)** r);

/**
 * \brief Swap the contents of two slist instances.
 *
 * \param left          The left slist instance for the swap.
 * \param right         The right slist instance for the swap.
 *
 * \note This operation always succeeds, as long as \p left and \p right are
 * valid. If either are invalid, the result of this operation is unpredictable
 * and will likely crash.
 *
 * \pre
 *      - \p left must point to a valid \ref slist instance.
 *      - \p right must point to a valid \ref slist instance.
 * \post
 *      - \p left contains and owns the contents previously contained and owned
 *      by \p right.
 *      - \p right contains and owns the contents previously contained and owned
 *      by \p left.
 */
void RCPR_SYM(slist_swap)(RCPR_SYM(slist)* left, RCPR_SYM(slist)* right);

/**
 * \brief Clear an slist instance, removing all nodes and their resources.
 *
 * \param l             The slist to clear.
 *
 * \pre
 *      - \p l must point to a valid \ref slist instance.
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
RCPR_SYM(slist_clear)(RCPR_SYM(slist)* l);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given an \ref slist instance, return the resource handle for this
 * \ref slist instance.
 *
 * \param list          The \ref slist instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref slist instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(slist_resource_handle)(
    RCPR_SYM(slist)* list);

/**
 * \brief Given an \ref slist_node instance, return the resource handle for this
 * \ref slist_node instance.
 *
 * \param node          The \ref slist_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref slist_node instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(slist_node_resource_handle)(
    RCPR_SYM(slist_node)* node);

/**
 * \brief Get the head of a \ref slist.
 *
 * \param node          Pointer to the \ref slist_node pointer to receive this
 *                      resource on success.
 * \param list          Pointer to the \ref slist under query.
 *
 * \note This \ref slist_node is owned by the \ref slist queried.  To take
 * ownership of this \ref slist_node, the caller must call \ref slist_remove to
 * remove this \ref slist_node from the \ref slist.  However, it is possible to
 * change the \ref resource owned by this \ref slist_node without first removing
 * it from the \ref slist by calling \ref slist_node_child_swap.
 *
 * If there is a head node, it is populated in \p node.  However, if this list
 * is empty, then \p node is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p node must not reference a valid \ref slist_node instance and must
 *        not be NULL.
 *      - \p slist must reference a valid \ref slist and must not be NULL.
 *
 * \post
 *      - On success, \p node is set to the head of the \ref slist, which can be
 *        NULL if \p list is empty.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_head)(
    RCPR_SYM(slist_node)** node, RCPR_SYM(slist)* list);

/**
 * \brief Get the tail of a \ref slist.
 *
 * \param node          Pointer to the \ref slist_node pointer to receive this
 *                      resource on success.
 * \param list          Pointer to the \ref slist under query.
 *
 * \note This \ref slist_node is owned by the \ref slist queried.  To take
 * ownership of this \ref slist_node, the caller must call \ref slist_remove to
 * remove this \ref slist_node from the \ref slist.  However, it is possible to
 * change the \ref resource owned by this \ref slist_node without first removing
 * it from the \ref slist by calling \ref slist_node_child_swap.
 *
 * If there is a tail node, it is populated in \p node.  However, if this list
 * is empty, then \p node is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p node must not reference a valid \ref slist_node instance and must
 *        not be NULL.
 *      - \p slist must reference a valid \ref slist and must not be NULL.
 *
 * \post
 *      - On success, \p node is set to the head of the \ref slist, which can be
 *        NULL if \p list is empty.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_tail)(
    RCPR_SYM(slist_node)** node, RCPR_SYM(slist)* list);

/**
 * \brief Get the count of nodes in an \ref slist.
 *
 * \param l             Pointer to the \ref slist under query.
 *
 * \returns the number of nodes in the given \ref slist.
 */
size_t
RCPR_SYM(slist_count)(
    RCPR_SYM(slist)* l);

/**
 * \brief Get the resource associated with the given of \ref slist_node.
 *
 * \param r             Pointer to the \ref resource pointer to receive this
 *                      child resource.
 * \param node          Pointer to the \ref slist_node under query.
 *
 * \note This \ref resource is owned by the \ref slist_node queried.  To take
 * ownership of this \ref resource, the caller must call \ref
 * slist_node_child_swap to remove this \ref resource from the \ref slist_node.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must not reference a valid \ref resource instance and must be
 *        NULL.
 *      - \p node must reference a valid \ref slist_node and must not be NULL.
 *
 * \post
 *      - On success, \p r is set to the child resource owned by \p node.
 *      - On failure, \p r is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_child)(
    RCPR_SYM(resource)** r, RCPR_SYM(slist_node)* node);

/**
 * \brief Given an \ref slist_node, return the next \ref slist_node in the list.
 *
 * \param next          Pointer to the \ref slist_node pointer to receive the
 *                      next value.
 * \param node          Pointer to the \ref slist_node under query.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p next must not reference a valid \ref slist_node instance and must
 *        be NULL.
 *      - \p node must reference a valid \ref slist_node and must not be NULL.
 *
 * \post
 *      - On success, \p next is set to the next node in this list, or NULL if
 *        \p node is the tail of the list.
 *      - On failure, \p next is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_next)(
    RCPR_SYM(slist_node)** next, RCPR_SYM(slist_node)* node);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref slist property.
 *
 * \param list           The \ref slist instance to be verified.
 *
 * \returns true if the \ref slist instance is valid.
 */
bool
RCPR_SYM(prop_slist_valid)(
    const RCPR_SYM(slist)* list);

/**
 * \brief Valid \ref slist_node property.
 *
 * \param node           The \ref slist_node instance to be verified.
 *
 * \returns true if the \ref slist_node instance is valid.
 */
bool
RCPR_SYM(prop_slist_node_valid)(
    const RCPR_SYM(slist_node)* node);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_slist_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(slist) sym ## slist; \
    typedef RCPR_SYM(slist_node) sym ## slist_node; \
    static inline status FN_DECL_MUST_CHECK sym ## slist_create( \
        RCPR_SYM(slist)** x, RCPR_SYM(allocator)* y) { \
            return RCPR_SYM(slist_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_insert_head( \
        RCPR_SYM(slist)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(slist_insert_head)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_append_tail( \
        RCPR_SYM(slist)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(slist_append_tail)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_append( \
        RCPR_SYM(slist_node)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(slist_append)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_node_child_swap( \
        RCPR_SYM(slist_node)* x, RCPR_SYM(resource)** y) { \
            return RCPR_SYM(slist_node_child_swap)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_pop( \
        RCPR_SYM(slist)* x, RCPR_SYM(resource)** y) { \
            return RCPR_SYM(slist_pop)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_node_next_pop( \
        RCPR_SYM(slist_node)* x, RCPR_SYM(resource)** y) { \
            return RCPR_SYM(slist_node_next_pop)(x,y); } \
    static inline void sym ## slist_swap( \
        RCPR_SYM(slist)* x, RCPR_SYM(slist)* y) { \
            RCPR_SYM(slist_swap)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_clear( \
        RCPR_SYM(slist)* x) { \
            return RCPR_SYM(slist_clear)(x); } \
    static inline RCPR_SYM(resource)* sym ## slist_resource_handle( \
        RCPR_SYM(slist)* x) { \
            return RCPR_SYM(slist_resource_handle)(x); } \
    static inline RCPR_SYM(resource)* sym ## slist_node_resource_handle( \
        RCPR_SYM(slist_node)* x) { \
            return RCPR_SYM(slist_node_resource_handle)(x); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_head( \
        RCPR_SYM(slist_node)** x, RCPR_SYM(slist)* y) { \
            return RCPR_SYM(slist_head)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_tail( \
        RCPR_SYM(slist_node)** x, RCPR_SYM(slist)* y) { \
            return RCPR_SYM(slist_tail)(x,y); } \
    static inline size_t sym ## slist_count( \
        RCPR_SYM(slist)* x) { \
            return RCPR_SYM(slist_count)(x); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_node_child( \
        RCPR_SYM(resource)** x, RCPR_SYM(slist_node)* y) { \
            return RCPR_SYM(slist_node_child)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## slist_node_next( \
        RCPR_SYM(slist_node)** x, RCPR_SYM(slist_node)* y) { \
            return RCPR_SYM(slist_node_next)(x,y); } \
    static inline bool sym ## prop_slist_valid( \
        const RCPR_SYM(slist)* x) { \
            return RCPR_SYM(prop_slist_valid)(x); } \
    static inline bool sym ## prop_slist_node_valid( \
        const RCPR_SYM(slist_node)* x) { \
            return RCPR_SYM(prop_slist_node_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_slist_as(sym) \
    __INTERNAL_RCPR_IMPORT_slist_sym(sym ## _)
#define RCPR_IMPORT_slist \
    __INTERNAL_RCPR_IMPORT_slist_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
