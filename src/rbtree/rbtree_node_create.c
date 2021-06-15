/**
 * \file rbtree/rbtree_node_create.c
 *
 * \brief Create a \ref rbtree_node instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/* forward decls. */
MODEL_STRUCT_TAG_GLOBAL_EXTERN(rbtree_node);
static status rbtree_node_release(resource* r);

/**
 * \brief Create a \ref rbtree_node instance from a tree and a resource.
 *
 * \param node          The pointer to pointer to receive the \ref rbtree_node
 *                      on success.
 * \param tree          The tree to which this \ref rbtree_node will belong.
 * \param r             The \ref resource to assign this node.
 *
 * \note On success, this function creates a new \ref rbtree_node, which is
 * owned by the caller until it is assigned to the \ref rbtree. If this
 * assignment should fail, it is the caller's responsibility to release this
 * resource.  On success, this node takes ownership of the resource and will
 * release it when it is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero failure code on failure.
 */
status FN_DECL_MUST_CHECK
rbtree_node_create(rbtree_node** node, rbtree* tree, RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != node);
    MODEL_ASSERT(prop_rbtree_valid(tree));
    MODEL_ASSERT(prop_resource_valid(r));

    /* attempt to allocate memory for this rbtree_node. */
    rbtree_node* tmp = NULL;
    int retval =
        allocator_allocate(tree->alloc, (void**)&tmp, sizeof(rbtree_node));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(rbtree_node));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);

    /* set the release method. */
    resource_init(&tmp->hdr, &rbtree_node_release);

    /* set the allocator. */
    tmp->alloc = tree->alloc;

    /* set the parent / left / right to nil to start. */
    tmp->parent = tmp->left = tmp->right = tree->nil;

    /* set the resource value. */
    tmp->value = r;

    /* set the node. */
    *node = tmp;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_rbtree_node_valid(*node));

    /* success. */
    return STATUS_SUCCESS;
}


/**
 * \brief Release a \ref rbtree_node resource.
 *
 * \param r             Pointer to the rbtree_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status rbtree_node_release(resource* r)
{
    rbtree_node* n = (rbtree_node*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_rbtree_node_valid(n));

    /* if the value is set, release it. */
    if (NULL != n->value)
    {
        resource* v = n->value;
        n->value = NULL;

        /* ensure that this value is valid. */
        MODEL_ASSERT(prop_resource_valid(v));

        /* release the value. */
        status retval = resource_release(v);
        if (STATUS_SUCCESS != retval)
            return retval;
    }

    /* clean up. */
    allocator* a = n->alloc;

    /* if reclaiming this rbtree_node succeeds, then so does this release. */
    return
        allocator_reclaim(a, n);
}
