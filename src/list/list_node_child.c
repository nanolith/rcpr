/**
 * \file list/list_node_child.c
 *
 * \brief Get the child resource associated with an \ref list_node.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

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
    RCPR_SYM(resource)** r, RCPR_SYM(list_node)* node)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != r);
    MODEL_ASSERT(prop_slist_node_valid(node));

    /* populate the resource with the child for this node. */
    *r = node->child;

    return STATUS_SUCCESS;
}
