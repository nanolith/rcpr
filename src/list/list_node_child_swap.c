/**
 * \file list/list_node_child_swap.c
 *
 * \brief Swap the \ref resource owned by this \ref list_node with the given
 * resource, replacing it with the value currently owned by this node.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

RCPR_IMPORT_list;
RCPR_IMPORT_resource;

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
    RCPR_SYM(list_node)* node, RCPR_SYM(resource)** r)
{
    resource* old;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_list_node_valid(node));
    RCPR_MODEL_ASSERT(NULL != r);
    RCPR_MODEL_ASSERT(prop_resource_valid(*r));

    /* save the old resource. */
    old = node->child;

    /* apply the new resource. */
    node->child = *r;

    /* swap with the old resource. */
    *r = old;

    /* success. */
    return STATUS_SUCCESS;
}
