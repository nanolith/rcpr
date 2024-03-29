/**
 * \file rcpr/queue.h
 *
 * \brief Simple queue container, backed by \ref slist.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/slist.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The queue container holds zero or more resources in a FIFO.
 */
typedef struct RCPR_SYM(queue) RCPR_SYM(queue);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref queue instance.
 *
 * \param q             Pointer to the \ref queue pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      queue resource and to allocate new nodes.
 *
 * \note This \ref queue is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref queue_resource_handle on this \ref queue instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p q must not reference a valid \ref queue instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p q is set to a pointer to a valid \ref queue instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On failure, \p q is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(queue_create)(
    RCPR_SYM(queue)** q, RCPR_SYM(allocator)* a);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Append the given \ref resource to the back of the \ref queue.
 *
 * \param q             Pointer to the \ref queue for the append operation.
 * \param r             Pointer to the \ref resource to append.
 *
 * \note After this operation, a queue node will be created to hold the
 * given \ref resource, and this node will become the tail of the \ref queue.
 * The \ref queue takes ownership of the \ref resource pointed to by \p r and
 * will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p q must be a valid \ref queue instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is appended to the tail of \p q.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(queue_append)(
    RCPR_SYM(queue)* q, RCPR_SYM(resource)* r);

/**
 * \brief Pop the head value of the \ref queue, setting the given resource
 * pointer to the resource previously held in the head node.
 *
 * The next node in the \ref queue after head becomes the new head node.
 *
 * \param q             Pointer to the \ref queue instance to pop.
 * \param r             Pointer to the \ref resource pointer to be set with the
 *                      head value.
 *
 * \note After this operation is complete, the \ref resource pointer pointer
 * passed to this function is set with the \ref resource from the popped
 * queue node.  This queue node is released; the caller assumes ownership of the
 * \ref resource and must release it when it is no longer needed.  If the \ref
 * resource pointer is NULL, then there was either no resource associated with
 * that node, or no node to pop.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p r must point to a valid resource pointer, set to NULL.
 *      - \p q must reference a valid \ref queue and must not be NULL.
 *
 * \post
 *      - On success, if \p queue has a at least one node, then
 *          - if the head node has a child \ref resource, then the pointer that
 *            \p r points to is set to that resource.
 *          - if the head node does not have a child \ref resource, then the
 *            pointer that \p r points to is set to NULL.
 *          - the head node is released, and the next node becomes the head
 *            node.
 *      - On failure, the pointer that \p r points to remains unchanged (NULL).
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(queue_pop)(
    RCPR_SYM(queue)* q, RCPR_SYM(resource)** r);

/**
 * \brief Place the given \ref resource at the front of the \ref queue.
 *
 * \param q             Pointer to the \ref queue for the insert operation.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After this operation, a queue node will be created to hold the
 * given \ref resource, and this node will become the head of the \ref queue.
 * The \ref queue takes ownership of the \ref resource pointed to by \p r and
 * will release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p q must be a valid \ref queue instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted to the head of \p q.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(queue_insert)(
    RCPR_SYM(queue)* q, RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given an \ref queue instance, return the count of nodes in that queue.
 *
 * \param q             The \ref queue instance for counting.
 *
 * \returns the number of nodes in the \ref queue instance.
 */
size_t
RCPR_SYM(queue_count)(
    RCPR_SYM(queue)* q);

/**
 * \brief Given an \ref queue instance, return the resource handle for this
 * \ref queue instance.
 *
 * \param q             The \ref queue instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref queue instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(queue_resource_handle)(
    RCPR_SYM(queue)* q);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref queue property.
 *
 * \param q             The \ref queue instance to be verified.
 *
 * \returns true if the \ref queue instance is valid.
 */
bool
RCPR_SYM(prop_queue_valid)(
    const RCPR_SYM(queue)* q);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_queue_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(queue) sym ## queue; \
    static inline status FN_DECL_MUST_CHECK sym ## queue_create( \
        RCPR_SYM(queue)** x, RCPR_SYM(allocator)* y) { \
            return RCPR_SYM(queue_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## queue_append( \
        RCPR_SYM(queue)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(queue_append)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## queue_pop( \
        RCPR_SYM(queue)* x, RCPR_SYM(resource)** y) { \
            return RCPR_SYM(queue_pop)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## queue_insert( \
        RCPR_SYM(queue)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(queue_insert)(x,y); } \
    static inline size_t sym ## queue_count( \
        RCPR_SYM(queue)* x) { \
            return RCPR_SYM(queue_count)(x); } \
    static inline RCPR_SYM(resource)* sym ## queue_resource_handle( \
        RCPR_SYM(queue)* x) { \
            return RCPR_SYM(queue_resource_handle)(x); } \
    static inline bool sym ## prop_queue_valid( \
        const RCPR_SYM(queue)* x) { \
            return RCPR_SYM(prop_queue_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_queue_as(sym) \
    __INTERNAL_RCPR_IMPORT_queue_sym(sym ## _)
#define RCPR_IMPORT_queue \
    __INTERNAL_RCPR_IMPORT_queue_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
