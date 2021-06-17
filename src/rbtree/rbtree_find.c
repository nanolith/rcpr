/**
 * \file rbtree/rbtree_find.c
 *
 * \brief Find a node in the tree matching a given key.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;

/**
 * \brief Find the given key in the \ref rbtree.
 *
 * \param r             Pointer to the pointer to the resource to be populated
 *                      after a successful find operation.
 * \param tree          Pointer to the \ref rbtree for the find operation.
 * \param key           Pointer to the key to find.
 *
 * \note After a successful find, the resource associated with the given key
 * will be populated in \p r. The resource ownership remains with the
 * \ref rbtree. If the key is not found, then \p r is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_RBTREE_NOT_FOUND if the key could not be found.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *      - \p r must be a valid pointer.
 *      - \p key must be a valid key for this \ref rbtree instance.
 *
 * \post
 *      - On success, \p r is set to the value in the tree associated with \p
 *        key.
 *      - On failure, \p r is set to NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_find)
    (RCPR_SYM(resource)** r, RCPR_SYM(rbtree)* tree, const void* key)
{
    rbtree_node* node;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_rbtree_valid(tree));
    MODEL_ASSERT(NULL != r);

    /* attempt to find the matching node. */
    status retval = rbtree_find_node(tree, key, &node);
    if (STATUS_SUCCESS != retval)
    {
        *r = NULL;
        return retval;
    }

    /* if the node is found, set the resource. */
    *r = node->value;

    return STATUS_SUCCESS;
}
