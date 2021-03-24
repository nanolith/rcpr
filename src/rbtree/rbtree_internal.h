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
    bool red;
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
 * \brief Given a \ref rbtree_node instance, return the resource handle for this
 * \ref rbtree_node instance.
 *
 * \param node          The \ref rbtree_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree_node instance.
 */
resource* rbtree_node_resource_handle(rbtree_node* node);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
