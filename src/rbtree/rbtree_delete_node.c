/**
 * \file rbtree/rbtree_delete_node.c
 *
 * \brief Delete a \ref rbtree_node from a \ref rbtree, optionally returning the
 * stored reference.
 *
 * \copyright 2026 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

/**
 * \brief Delete the given \ref rbtree_node from the \ref rbtree, optionally
 * releasing the resource.
 *
 * \param r             Pointer to the pointer to the resource to be populated
 *                      after a successful delete operation. If this pointer
 *                      pointer is NULL, then the resource is released.
 * \param tree          Pointer to the \ref rbtree for the delete operation.
 * \param node          Pointer to the node to delete.
 *
 * \note After a successful delete, the resource associated with the given key
 * will be populated in \p r, if \p r is not NULL.  Otherwise, the resource is
 * released.  If \p r is populated, then ownership of this \ref resource
 * transfers to the caller, and the caller must release this \ref resource by
 * calling \ref resource_release on it when it is no longer needed.
 *
 * \note \p node MUST be associated with this tree, or bad things will happen.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *      - \p r is optional, and can be NULL if the caller wishes to just release
 *        the resource.
 *      - \p node must be a valid \ref rbtree_node associated with this
 *        \ref rbtree instance.
 *
 * \post
 *      - On success, \p r is set to the value in the tree associated with \p
 *        key.
 *      - On failure, \p r is set to NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_delete_node)(
    RCPR_SYM(resource)** r, RCPR_SYM(rbtree)* tree,
    RCPR_SYM(rbtree_node)* node)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_rbtree_valid(tree));

    /* if the node is found, then remove it from the tree. */
    rbtree_remove_node(tree, node);

    /* if the resource pointer pointer is set, then transfer ownership. */
    if (NULL != r)
    {
        *r = node->value;
        node->value = NULL;
    }

    /* clean up the node, returning the cleanup status to the caller. */
    return
        resource_release(rbtree_node_resource_handle(node));
}
