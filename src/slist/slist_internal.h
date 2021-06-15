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

struct slist
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(slist);

    RCPR_SYM(allocator)* alloc;
    slist_node* head;
    slist_node* tail;
    size_t count;
};

struct slist_node
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(slist_node);

    RCPR_SYM(allocator)* alloc;
    slist* parent;
    slist_node* next;
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
slist_node_create(
    slist_node** node, slist* list, RCPR_SYM(resource)* r);

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
status slist_node_cleanup(RCPR_SYM(allocator)* a, slist_node* node);

/**
 * \brief Release an slist_node resource.
 *
 * \param r             Pointer to the slist_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status slist_node_release(RCPR_SYM(resource)* r);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
