/**
 * \file rbtree/rbtree_find_node.c
 *
 * \brief Find a node in the tree matching a given key.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

/**
 * \brief Find a \ref rbtree_node matching the given key in an \ref rbtree
 * instance.
 *
 * On success, the \ref rbtree_node pointer pointer is updated with the pointer
 * to the found \ref rbtree_node.  On failure, an error code is returned.
 *
 * \param tree          The \ref rbtree instance to search.
 * \param key           The key to search for.
 * \param node          Pointer to the pointer to receive the \ref rbtree_node
 *                      on search success.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_RBTREE_NOT_FOUND if a matching node was not found.
 */
status FN_DECL_MUST_CHECK
rbtree_find_node(rbtree* tree, const void* key, rbtree_node** node)
{
    rbtree_node* x = tree->root;

    while (x != tree->nil)
    {
        const void* x_key = tree->key(tree->context, x->value);

        int compare_result = tree->compare(tree->context, key, x_key);
        if (compare_result == RCPR_COMPARE_EQ)
        {
            *node = x;
            return STATUS_SUCCESS;
        }
        else if (compare_result == RCPR_COMPARE_LT)
        {
            x = x->left;
        }
        else
        {
            x = x->right;
        }
    }

    return ERROR_RBTREE_NOT_FOUND;
}
