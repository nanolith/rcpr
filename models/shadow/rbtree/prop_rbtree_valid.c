/**
 * \file models/shadow/rbtree/prop_rbtree_valid.c
 *
 * \brief Check whether an rbtree instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/rbtree/rbtree_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(rbtree);

/**
 * \brief Valid \ref rbtree property.
 *
 * \param tree          The \ref rbtree instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool prop_rbtree_valid(const rbtree* tree)
{
    MODEL_ASSERT(NULL != tree);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        tree->MODEL_STRUCT_TAG_REF(rbtree), rbtree);

    return
        prop_resource_valid(&tree->hdr)
     && (tree->root == tree->nil || prop_rbtree_node_valid(tree, tree->root))
     && prop_allocator_valid(tree->alloc)
     && (tree->compare != NULL)
     && (tree->key != NULL);
}
