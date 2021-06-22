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

typedef struct RCPR_SYM(rbtree_node) RCPR_SYM(rbtree_node);

struct RCPR_SYM(rbtree_node)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(rbtree_node);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(rbtree_node)* parent;
    RCPR_SYM(rbtree_node)* left;
    RCPR_SYM(rbtree_node)* right;
    RCPR_SYM(resource)* value;
    bool color;
};

struct RCPR_SYM(rbtree)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(rbtree);

    RCPR_SYM(allocator)* alloc;
    void* context;
    RCPR_SYM(compare_fn) compare;
    RCPR_SYM(compare_key_fn) key;
    RCPR_SYM(rbtree_node)* root;
    RCPR_SYM(rbtree_node) nil_impl;
    RCPR_SYM(rbtree_node)* nil;
    size_t count;
};

/**
 * \brief Perform a left rotation on a subtree in the given tree.
 *
 * \param tree          The \ref rbtree on which this operation is being
 *                      performed.
 * \param x             The pivot point node for this left rotation.
 */
void
RCPR_SYM(rbtree_left_rotate)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x);

/**
 * \brief Perform a right rotation on a subtree in the given tree.
 *
 * \param tree          The \ref rbtree on which this operation is being
 *                      performed.
 * \param y             The pivot point node for this right rotation.
 */
void
RCPR_SYM(rbtree_right_rotate)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* y);

/**
 * \brief Perform a post-insert fixup of the given \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance to fix up.
 * \param z             The inserted node where the fixup starts.
 */
void
RCPR_SYM(rbtree_insert_fixup)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* z);

/**
 * \brief Transplant moves subtrees around when a node with two children is
 * deleted.
 *
 * \param tree          The \ref rbtree instance on which the transplant is
 *                      occurring.
 * \param u             One node that is part of the transplant operation.
 * \param v             The other node that is part of the transplant operation.
 */
void
RCPR_SYM(rbtree_transplant)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* u, RCPR_SYM(rbtree_node)* v);

/**
 * \brief Return the minimum node in an rbtree subtree.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which the search should start.
 *
 * \returns the minimum node in this subtree.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_minimum_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x);

/**
 * \brief Return the maximum node in an rbtree subtree.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which the search should start.
 *
 * \returns the maximum node in this subtree.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_maximum_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x);

/**
 * \brief Return the in-order successor node of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which a successor is found.
 *
 * \returns the successor node of this node, or tree->nil if none is found.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_successor_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x);

/**
 * \brief Return the in-order predecessor node of the given node.
 *
 * \param tree          The \ref rbtree instance.
 * \param x             The \ref rbtree_node from which a predecessor is found.
 *
 * \returns the predecessor node of this node, or tree->nil if none is found.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_predecessor_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x);

/**
 * \brief Perform a post-delete fixup of the given \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance to fix up.
 * \param x             The node now occupying the deleted node's position.
 */
void
RCPR_SYM(rbtree_delete_fixup)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* x);

/**
 * \brief Remove the given \ref rbtree_node from the \ref rbtree.
 *
 * After the completion of this call, the resource pointed to by \p z is owned
 * by the caller and must be released when no longer needed.
 *
 * \param tree          The \ref rbtree instance from which the node is removed.
 * \param z             The \ref rbtree_node to delete from the tree.
 */
void
RCPR_SYM(rbtree_remove_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* z);

/**
 * \brief Insert the given \ref rbtree_node into the \ref rbtree.
 *
 * After the completion of this call, the resource pointed to by \p z is owned
 * by the tree and will be released when it is released.
 *
 * \param tree          The \ref rbtree instance from which the node is removed.
 * \param z             The \ref rbtree_node to delete from the tree.
 */
void
RCPR_SYM(rbtree_insert_node)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* z);

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
RCPR_SYM(rbtree_find_node)(
    RCPR_SYM(rbtree)* tree, const void* key, RCPR_SYM(rbtree_node)** node);

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
RCPR_SYM(rbtree_node_create)(
    RCPR_SYM(rbtree_node)** node, RCPR_SYM(rbtree)* tree,
    RCPR_SYM(resource)* r);

/**
 * \brief Given a \ref rbtree_node instance, return the resource handle for this
 * \ref rbtree_node instance.
 *
 * \param node          The \ref rbtree_node instance from which the resource
 *                      handle is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree_node instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(rbtree_node_resource_handle)(
    RCPR_SYM(rbtree_node)* node);

/**
 * \brief Valid \ref rbtree_node property.
 *
 * \param tree          The \ref rbtree instance to which this \ref rbtree_node
 *                      belongs.
 * \param node          The \ref rbtree_node instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool
RCPR_SYM(prop_rbtree_node_valid)(
    const RCPR_SYM(rbtree)* tree, const RCPR_SYM(rbtree_node)* node);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_rbtree_internal \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"") \
    typedef RCPR_SYM(rbtree_node) rbtree_node; \
    static inline void rbtree_left_rotate( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            RCPR_SYM(rbtree_left_rotate)(x,y); } \
    static inline void rbtree_right_rotate( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            RCPR_SYM(rbtree_right_rotate)(x,y); } \
    static inline void rbtree_insert_fixup( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            RCPR_SYM(rbtree_insert_fixup)(x,y); } \
    static inline void rbtree_transplant( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y, \
        RCPR_SYM(rbtree_node)* z) { \
            RCPR_SYM(rbtree_transplant)(x,y,z); } \
    static inline RCPR_SYM(rbtree_node)* rbtree_minimum_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_minimum_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* rbtree_maximum_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_maximum_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* rbtree_successor_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_successor_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* rbtree_predecessor_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_predecessor_node)(x,y); } \
    static inline void rbtree_delete_fixup( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            RCPR_SYM(rbtree_delete_fixup)(x,y); } \
    static inline void rbtree_remove_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            RCPR_SYM(rbtree_remove_node)(x,y); } \
    static inline void rbtree_insert_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            RCPR_SYM(rbtree_insert_node)(x,y); } \
    static inline status FN_DECL_MUST_CHECK rbtree_find_node( \
        RCPR_SYM(rbtree)* x, const void* y, RCPR_SYM(rbtree_node)** z) { \
            return RCPR_SYM(rbtree_find_node)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK rbtree_node_create( \
        RCPR_SYM(rbtree_node)** x, RCPR_SYM(rbtree)* y, \
        RCPR_SYM(resource)* z) { \
            return RCPR_SYM(rbtree_node_create)(x,y,z); } \
    static inline RCPR_SYM(resource)* rbtree_node_resource_handle( \
        RCPR_SYM(rbtree_node)* x) { \
            return RCPR_SYM(rbtree_node_resource_handle)(x); } \
    static inline bool prop_rbtree_node_valid( \
        const RCPR_SYM(rbtree)* x, const RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(prop_rbtree_node_valid)(x,y); } \
    _Pragma("GCC diagnostic pop") \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
