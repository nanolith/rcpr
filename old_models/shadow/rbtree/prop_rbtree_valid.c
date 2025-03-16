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

RCPR_IMPORT_allocator;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_rbtree_internal;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(rbtree);

/**
 * \brief Valid \ref rbtree property.
 *
 * \param tree          The \ref rbtree instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool RCPR_SYM(prop_rbtree_valid)(const rbtree* tree)
{
    RCPR_MODEL_ASSERT(NULL != tree);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        tree->RCPR_MODEL_STRUCT_TAG_REF(rbtree), rbtree);

    if (tree->nil != tree->root)
    {
        RCPR_MODEL_ASSERT(prop_rbtree_node_valid(tree, tree->root));
    }

    return
        prop_resource_valid(&tree->hdr)
     && prop_allocator_valid(tree->alloc)
     && (tree->compare != NULL)
     && (tree->key != NULL);
}
