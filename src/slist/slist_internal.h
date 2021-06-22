/**
 * \file slist/slist_internal.h
 *
 * \brief Internal data types and functions for slist.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/slist.h>
#include <rcpr/resource.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(slist)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(slist);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(slist_node)* head;
    RCPR_SYM(slist_node)* tail;
    size_t count;
};

struct RCPR_SYM(slist_node)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(slist_node);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(slist)* parent;
    RCPR_SYM(slist_node)* next;
    RCPR_SYM(resource)* child;
};

/**
 * \brief Create a \ref slist_node instance.
 *
 * \param node          Pointer to the \ref slist_node pointer to receive this
 *                      resource on success.
 * \param list          Pointer to the parent \ref slist instance.
 * \param r             Pointer to the child \ref resource instance.
 *
 * \note This \ref slist_node is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * slist_node_resource_handle on this \ref slist_node instance.  If \p r is not
 * NULL, then it must be a valid \ref reference instance.  The node takes
 * ownership of this reference.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must not reference a valid list node instance and must not be
 *        NULL.
 *      - \p list must reference a valid list instance.
 *      - \p r must either reference a valid resource instance or be NULL.
 *
 * \post
 *      - On success, \p node is set to a pointer to a valid \ref slist_node
 *        instance, which is a \ref resource owned by the \p list.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_create)(
    RCPR_SYM(slist_node)** node, RCPR_SYM(slist)* list, RCPR_SYM(resource)* r);

/**
 * \brief Clean up an slist node.
 *
 * \param a             Pointer to the slist allocator.
 * \param node          Pointer to the slist_node to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status
RCPR_SYM(slist_node_cleanup)(
    RCPR_SYM(allocator)* a, RCPR_SYM(slist_node)* node);

/**
 * \brief Release an slist_node resource.
 *
 * \param r             Pointer to the slist_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status
RCPR_SYM(slist_node_release)(
    RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/
#define RCPR_IMPORT_slist_internal \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"") \
    static inline status FN_DECL_MUST_CHECK slist_node_create( \
        RCPR_SYM(slist_node)** x, RCPR_SYM(slist)* y, \
        RCPR_SYM(resource)* z) { \
            return RCPR_SYM(slist_node_create)(x,y,z); } \
    static inline status slist_node_cleanup( \
        RCPR_SYM(allocator)* x, RCPR_SYM(slist_node)* y) { \
            return RCPR_SYM(slist_node_cleanup)(x,y); } \
    static inline status slist_node_release( \
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(slist_node_release)(x); } \
    _Pragma("GCC diagnostic pop") \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
