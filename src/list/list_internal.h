/**
 * \file list/list_internal.h
 *
 * \brief Internal data types and functions for list.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/list.h>
#include <rcpr/resource.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct list
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(list);

    RCPR_SYM(allocator)* alloc;
    list_node* head;
    list_node* tail;
    size_t count;
};

struct list_node
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(list_node);

    RCPR_SYM(allocator)* alloc;
    list* parent;
    list_node* prev;
    list_node* next;
    RCPR_SYM(resource)* child;
};

/**
 * \brief Create a \ref list_node instance.
 *
 * \param node          Pointer to the \ref list_node pointer to receive this
 *                      resource on success.
 * \param l             Pointer to the parent \ref list instance.
 * \param r             Pointer to the child \ref resource instance.
 *
 * \note This \ref list_node is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * list_node_resource_handle on this \ref list_node instance.  If \p r is not
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
 *      - \p l must reference a valid list instance.
 *      - \p r must either reference a valid resource instance or be NULL.
 *
 * \post
 *      - On success, \p node is set to a pointer to a valid \ref list_node
 *        instance, which is a \ref resource owned by the \p l.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
list_node_create(
    list_node** node, list* l, RCPR_SYM(resource)* r);

/**
 * \brief Clean up a list node.
 *
 * \param a             Pointer to the list allocator.
 * \param node          Pointer to the list_node to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status list_node_cleanup(RCPR_SYM(allocator)* a, list_node* node);

/**
 * \brief Release an list_node resource.
 *
 * \param r             Pointer to the list_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status list_node_release(RCPR_SYM(resource)* r);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
