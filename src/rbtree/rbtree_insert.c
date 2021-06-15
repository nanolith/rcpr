/**
 * \file rbtree/rbtree_insert.c
 *
 * \brief Insert a node into a red-black tree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Insert the given \ref resource into the \ref rbtree.
 *
 * \param tree          Pointer to the \ref rbtree for the insert operation.
 * \param r             Pointer to the \ref resource to insert.
 *
 * \note After a successful insert, a \ref rbtree_node will be created to hold
 * the given \ref resource, and this node will be placed in the tree. The \ref
 * rbtree takes ownership of the \ref resource pointed to by \p r and will
 * release it when it is released.  If the insert fails, then the caller retains
 * ownership of \p r and must release it when no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *      - ERROR_RBTREE_DUPLICATE if a duplicate item already exists in the
 *        \ref rbtree.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *      - \p r must be a valid \ref resource instance.
 *
 * \post
 *      - On success, \p r is inserted into \p tree.
 *      - On failure, \p r remains owned by the caller.
 */
status FN_DECL_MUST_CHECK
rbtree_insert(rbtree* tree, RCPR_SYM(resource)* r)
{
    status retval;
    rbtree_node* new_node = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_rbtree_valid(tree));
    MODEL_ASSERT(prop_resource_valid(r));

    /* attempt to create an rbtree node. */
    retval = rbtree_node_create(&new_node, tree, r);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* insert the node into the tree. */
    rbtree_insert_node(tree, new_node);

    /* success. */
    return STATUS_SUCCESS;
}
