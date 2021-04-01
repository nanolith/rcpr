/**
 * \file rbtree/rbtree_internal.h
 *
 * \brief Internal data types and functions for rbtree.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/rbtree.h>
#include <rcpr/model_assert.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

#define RBTREE_RED true
#define RBTREE_BLACK false

typedef struct rbtree_node rbtree_node;

struct rbtree_node
{
    resource hdr;

    MODEL_STRUCT_TAG(rbtree_node);

    allocator* alloc;
    rbtree_node* parent;
    rbtree_node* left;
    rbtree_node* right;
    resource* value;
    bool color;
};

struct rbtree
{
    resource hdr;

    MODEL_STRUCT_TAG(rbtree);

    allocator* alloc;
    void* context;
    compare_fn compare;
    compare_key_fn key;
    rbtree_node* root;
    rbtree_node nil_impl;
    rbtree_node* nil;
};

/**
 * \brief Perform a left rotation on a subtree in the given tree.
 *
 * \param tree          The \ref rbtree on which this operation is being
 *                      performed.
 * \param x             The pivot point node for this left rotation.
 */
void rbtree_left_rotate(rbtree* tree, rbtree_node* x);

/**
 * \brief Perform a right rotation on a subtree in the given tree.
 *
 * \param tree          The \ref rbtree on which this operation is being
 *                      performed.
 * \param y             The pivot point node for this right rotation.
 */
void rbtree_right_rotate(rbtree* tree, rbtree_node* y);

/**
 * \brief Perform a post-insert fixup of the given \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance to fix up.
 * \param z             The inserted node where the fixup starts.
 */
void rbtree_insert_fixup(rbtree* tree, rbtree_node* z);

/**
 * \brief Transplant moves subtrees around when a node with two children is
 * deleted.
 *
 * \param tree          The \ref rbtree instance on which the transplant is
 *                      occurring.
 * \param u             One node that is part of the transplant operation.
 * \param v             The other node that is part of the transplant operation.
 */
void rbtree_transplant(rbtree* tree, rbtree_node* u, rbtree_node* v);

/**
 * \brief Return the minimum node in an rbtree subtree.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which the search should start.
 *
 * \returns the minimum node in this subtree.
 */
rbtree_node* rbtree_minimum_node(rbtree* tree, rbtree_node* x);

/**
 * \brief Return the maximum node in an rbtree subtree.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which the search should start.
 *
 * \returns the maximum node in this subtree.
 */
rbtree_node* rbtree_maximum_node(rbtree* tree, rbtree_node* x);

/**
 * \brief Return the in-order successor node of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which a successor is found.
 *
 * \returns the successor node of this node, or tree->nil if none is found.
 */
rbtree_node* rbtree_successor_node(rbtree* tree, rbtree_node* x);

/**
 * \brief Return the in-order predecessor node of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which a predecessor is found.
 *
 * \returns the predecessor node of this node, or tree->nil if none is found.
 */
rbtree_node* rbtree_predecessor_node(rbtree* tree, rbtree_node* x);

/**
 * \brief Perform a post-delete fixup of the given \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance to fix up.
 * \param x             The node now occupying the deleted node's position.
 */
void rbtree_delete_fixup(rbtree* tree, rbtree_node* x);

/**
 * \brief Given a \ref rbtree_node instance, return the resource handle for this
 * \ref rbtree_node instance.
 *
 * \param node          The \ref rbtree_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree_node instance.
 */
resource* rbtree_node_resource_handle(rbtree_node* node);

/**
 * \brief Valid \ref rbtree_node property.
 *
 * \param tree          The \ref rbtree instance to which this \ref rbtree_node
 *                      belongs.
 * \param node          The \ref rbtree_node instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool prop_rbtree_node_valid(const rbtree* tree, const rbtree_node* node);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
