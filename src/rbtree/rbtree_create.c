/**
 * \file rbtree/rbtree_create.c
 *
 * \brief Create an rbtree instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "rbtree_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/* forward decls. */
MODEL_STRUCT_TAG_GLOBAL_EXTERN(rbtree);
static status rbtree_resource_release(resource* r);
static status rbtree_nil_node_resource_release(resource* r);
static status rbtree_delete_nodes(rbtree* tree, rbtree_node* n);

/**
 * \brief Create an \ref rbtree instance.
 *
 * \param tree          Pointer to the \ref rbtree pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      rbtree resource.
 * \param compare       The \ref compare_fn to use to compare two keys in this
 *                      \ref rbtree instance.
 * \param key           The function to get a key from a resource.
 * \param context       Pointer to the context to pass to the comparison
 *                      function.
 *
 * \note This \ref rbtree is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref rbtree_resource_handle on this \ref rbtree instance.
 *
 * Any resource added to this \ref rbtree via \ref rbtree_insert is owned by the
 * \ref rbtree and will be released when the \ref rbtree resource handle is
 * released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p tree must not reference a valid \ref tree instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p compare must reference a valid \ref compare_fn function.
 *
 * \post
 *      - On success, \p tree is set to a pointer to a valid \ref rbtree
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p tree is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
rbtree_create(
    rbtree** tree, RCPR_SYM(allocator)* a, compare_fn compare,
    compare_key_fn key, void* context)
{
    rbtree* tmp;
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != tree);
    MODEL_ASSERT(NULL != a);

    /* attempt to allocate memory for this rbtree instance. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(rbtree));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(rbtree));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(rbtree), rbtree);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(rbtree), rbtree);

    /* set the release method. */
    resource_init(&tmp->hdr, &rbtree_resource_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->context = context;
    tmp->compare = compare;
    tmp->key = key;
    resource_init(&tmp->nil_impl.hdr, &rbtree_nil_node_resource_release);
    tmp->nil = &tmp->nil_impl;
    tmp->nil->parent = tmp->nil;
    tmp->nil->left = tmp->nil;
    tmp->nil->right = tmp->nil;
    tmp->nil->value = rbtree_node_resource_handle(tmp->nil);
    tmp->root = tmp->nil;

    /* set the return pointer. */
    *tree = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_rbtree_valid(*tree));

    /* success. */
    goto done;

done:
    return retval;
}

/**
 * \brief Release an rbtree resource.
 *
 * \param r         The rbtree resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status rbtree_resource_release(resource* r)
{
    status delete_nodes_retval = STATUS_SUCCESS;
    rbtree* tree = (rbtree*)r;

    /* cache the allocator. */
    allocator* a = tree->alloc;

    /* clean up all nodes. */
    if (tree->root != tree->nil)
    {
        delete_nodes_retval = rbtree_delete_nodes(tree, tree->root);
    }

    /* clear the rbtree structure. */
    MODEL_EXEMPT(memset(tree, 0, sizeof(*tree)));

    /* reclaim the rbtree structure. */
    status reclaim_retval = allocator_reclaim(a, tree);

    /* if any operation failed, return a failure code. */
    if (STATUS_SUCCESS != delete_nodes_retval)
    {
        return delete_nodes_retval;
    }
    else if (STATUS_SUCCESS != reclaim_retval)
    {
        return reclaim_retval;
    }

    return STATUS_SUCCESS;
}

/**
 * \brief Delete all nodes in this subtree, including this node.
 *
 * \param tree      The tree to which this subtree belongs.
 * \param n         The subtree to delete.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status rbtree_delete_nodes(rbtree* tree, rbtree_node* n)
{
    status retval_left = STATUS_SUCCESS;
    status retval_right = STATUS_SUCCESS;

    /* recursively delete the left branch. */
    if (tree->nil != n->left)
    {
        retval_left = rbtree_delete_nodes(tree, n->left);
    }

    /* recursively delete the right branch. */
    if (tree->nil != n->right)
    {
        retval_right = rbtree_delete_nodes(tree, n->right);
    }

    /* release this node. */
    status retval_node = resource_release(rbtree_node_resource_handle(n));

    /* if any operation failed, return a failure code. */
    if (STATUS_SUCCESS != retval_left)
        return retval_left;
    else if (STATUS_SUCCESS != retval_right)
        return retval_right;
    else if (STATUS_SUCCESS != retval_node)
        return retval_node;

    return STATUS_SUCCESS;
}

/**
 * \brief Dummy resource release for the nil node.
 *
 * \param r         The rbtree_node nil node.
 *
 * \returns a failure code.
 *      - ERROR_RBTREE_NIL_NODE_CANNOT_BE_RELEASED on failure.
 */
static status rbtree_nil_node_resource_release(resource* r)
{
    (void)r;

    return ERROR_RBTREE_NIL_NODE_CANNOT_BE_RELEASED;
}
