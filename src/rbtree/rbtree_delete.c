/**
 * \file rbtree/rbtree_delete.c
 *
 * \brief Delete a key from a \ref rbtree, optionally returning the stored
 * reference.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

/**
 * \brief Delete the given key from the \ref rbtree, optionally releasing the
 * resource.
 *
 * \param r             Pointer to the pointer to the resource to be populated
 *                      after a successful delete operation. If this pointer
 *                      pointer is NULL, then the resource is released.
 * \param tree          Pointer to the \ref rbtree for the delete operation.
 * \param key           Pointer to the key to delete.
 *
 * \note After a successful delete, the resource associated with the given key
 * will be populated in \p r, if \p r is not NULL.  Otherwise, the resource is
 * released.  If \p r is populated, then ownership of this \ref resource
 * transfers to the caller, and the caller must release this \ref resource by
 * calling \ref resource_release on it when it is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_RBTREE_NOT_FOUND if the key could not be found.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *      - \p r is optional, and can be NULL if the caller wishes to just release
 *        the resource.
 *      - \p key must be a valid key for this \ref rbtree instance.
 *
 * \post
 *      - On success, \p r is set to the value in the tree associated with \p
 *        key.
 *      - On failure, \p r is set to NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_delete)(
    RCPR_SYM(resource)** r, RCPR_SYM(rbtree)* tree, const void* key)
{
    status retval;
    rbtree_node* node = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_rbtree_valid(tree));

    /* attempt to find a node matching the given key. */
    retval = rbtree_find_node(tree, key, &node);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

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
