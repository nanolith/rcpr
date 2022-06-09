/**
 * \file rcpr/rbtree.h
 *
 * \brief The RCPR red/black tree library.
 *
 * \copyright 2021-2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/compare.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief An rbtree stores resources in a balanced binary tree.
 */
typedef struct RCPR_SYM(rbtree) RCPR_SYM(rbtree);

/**
 * \brief An rbtree_node represents a single node in the binary tree.
 */
typedef struct RCPR_SYM(rbtree_node) RCPR_SYM(rbtree_node);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

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
RCPR_SYM(rbtree_create)(
    RCPR_SYM(rbtree)** tree, RCPR_SYM(allocator)* a,
    RCPR_SYM(compare_fn) compare, RCPR_SYM(compare_key_fn) key, void* context);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

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
RCPR_SYM(rbtree_insert)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(resource)* r);

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
RCPR_SYM(rbtree_find)(
    RCPR_SYM(resource)** r, RCPR_SYM(rbtree)* tree, const void* key);

/**
 * \brief Delete the given key from the \ref rbtree, optionally releasing the
 * resource.
 *
 * \param r             Pointer to the pointer to the resource to be populated
 *                      after a successful delete operation. If this pointer
 *                      pointer is NULL, then the resource is released.
 * \param tree          Pointer to the \ref rbtree for the delete operation.
 * \param key           Pointer to the key to delete.
 *
 * \note After a successful delete, the resource associated with the given key
 * will be populated in \p r, if \p r is not NULL.  Otherwise, the resource is
 * released.  If \p r is populated, then ownership of this \ref resource
 * transfers to the caller, and the caller must release this \ref resource by
 * calling \ref resource_release on it when it is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_RBTREE_NOT_FOUND if the key could not be found.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *      - \p r is optional, and can be NULL if the caller wishes to just release
 *        the resource.
 *      - \p key must be a valid key for this \ref rbtree instance.
 *
 * \post
 *      - On success, \p r is set to the value in the tree associated with \p
 *        key.
 *      - On failure, \p r is set to NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_delete)(
    RCPR_SYM(resource)** r, RCPR_SYM(rbtree)* tree, const void* key);

/**
 * \brief Clear all entries from an rbtree instance, releasing resources held by
 * all nodes.
 *
 * \param tree          Pointer to the \ref rbtree for the clear operation.
 *
 * \note After a successful clear, all resources associated with nodes in this
 * \ref rbtree instance are released.  All nodes are pruned.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p tree must be a valid \ref rbtree instance.
 *
 * \post
 *      - On success, all nodes in \p tree as well as all resources held by
 *        those nodes are released.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(rbtree_clear)(
    RCPR_SYM(rbtree)* tree);

/**
 * \brief Swap the contents of two rbtree instances.
 *
 * \param left          The left rbtree instance for the swap.
 * \param right         The right rbtree instance for the swap.
 *
 * \note This operation always succeeds, as long as \p left and \p right are
 * valid. If either are invalid, the result of this operation is unpredictable
 * and will likely crash.
 *
 * \pre
 *      - \p left must point to a valid \ref rbtree instance.
 *      - \p right must point to a valid \ref rbtree instance.
 * \post
 *      - \p left contains and owns the contents previously contained and owned
 *      by \p right
 *      - \p right contains and owns the contents previously contained and owned
 *      by \p left.
 */
void RCPR_SYM(rbtree_swap)(RCPR_SYM(rbtree)* left, RCPR_SYM(rbtree)* right);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

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
 * \brief Return the nil node pointer for the tree.
 *
 * \param tree          The \ref rbtree instance.
 *
 * \returns the nil pointer for this tree.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_nil_node)(
    RCPR_SYM(rbtree)* tree);

/**
 * \brief Return the root node pointer for the tree.
 *
 * \param tree          The \ref rbtree instance.
 *
 * \returns the root pointer for this tree.
 */
RCPR_SYM(rbtree_node)*
RCPR_SYM(rbtree_root_node)(
    RCPR_SYM(rbtree)* tree);

/**
 * \brief Return the value associated with a given rbtree node.
 *
 * \note Ownership of this value remains with the \ref rbtree_node.
 *
 * \param tree          The \ref rbtree instance.
 * \param node          The \ref rbtree_node accessed.
 *
 * \returns the resource associated with this node.
 */
RCPR_SYM(resource)*
RCPR_SYM(rbtree_node_value)(
    RCPR_SYM(rbtree)* tree, RCPR_SYM(rbtree_node)* node);

/**
 * \brief Return the count of elements currently in this \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance.
 *
 * \returns the count of elements in the \ref rbtree instance.
 */
size_t
RCPR_SYM(rbtree_count)(
    RCPR_SYM(rbtree)* tree);

/**
 * \brief Given a \ref rbtree instance, return the resource handle for this
 * \ref rbtree instance.
 *
 * \param tree          The \ref rbtree instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref rbtree instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(rbtree_resource_handle)(
    RCPR_SYM(rbtree)* tree);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref rbtree property.
 *
 * \param tree          The \ref rbtree instance to be verified.
 *
 * \returns true if the \ref rbtree instance is valid.
 */
bool
RCPR_SYM(prop_rbtree_valid)(
    const RCPR_SYM(rbtree)* tree);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_rbtree_as(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(rbtree) sym ## _ ## rbtree; \
    typedef RCPR_SYM(rbtree_node) sym ## _ ## rbtree_node; \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## rbtree_create( \
        RCPR_SYM(rbtree)** v, RCPR_SYM(allocator)* w, \
        RCPR_SYM(compare_fn) x, RCPR_SYM(compare_key_fn) y, void* z) { \
            return RCPR_SYM(rbtree_create)(v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## rbtree_insert( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(rbtree_insert)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## rbtree_find( \
        RCPR_SYM(resource)** x, RCPR_SYM(rbtree)* y, const void* z) { \
            return RCPR_SYM(rbtree_find)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## rbtree_delete( \
        RCPR_SYM(resource)** x, RCPR_SYM(rbtree)* y, const void* z) { \
            return RCPR_SYM(rbtree_delete)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## rbtree_clear( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_clear)(x); } \
    static inline void sym ## _ ## rbtree_swap( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree)* y) { \
            return RCPR_SYM(rbtree_swap)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* sym ## _ ## rbtree_minimum_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_minimum_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* sym ## _ ## rbtree_maximum_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_maximum_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* sym ## _ ## rbtree_successor_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_successor_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* sym ## _ ## rbtree_predecessor_node( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_predecessor_node)(x,y); } \
    static inline RCPR_SYM(rbtree_node)* sym ## _ ## rbtree_nil_node( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_nil_node)(x); } \
    static inline RCPR_SYM(rbtree_node)* sym ## _ ## rbtree_root_node( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_root_node)(x); } \
    static inline RCPR_SYM(resource)* sym ## _ ## rbtree_node_value( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_node_value)(x,y); } \
    static inline size_t sym ## _ ## rbtree_count( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_count)(x); } \
    static inline RCPR_SYM(resource)* sym ## _ ## rbtree_resource_handle( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_resource_handle)(x); } \
    static inline bool sym ## _ ## prop_rbtree_valid( \
        const RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(prop_rbtree_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_rbtree \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(rbtree) rbtree; \
    typedef RCPR_SYM(rbtree_node) rbtree_node; \
    static inline status FN_DECL_MUST_CHECK rbtree_create( \
        RCPR_SYM(rbtree)** v, RCPR_SYM(allocator)* w, \
        RCPR_SYM(compare_fn) x, RCPR_SYM(compare_key_fn) y, void* z) { \
            return RCPR_SYM(rbtree_create)(v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK rbtree_insert( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(resource)* y) { \
            return RCPR_SYM(rbtree_insert)(x,y); } \
    static inline status FN_DECL_MUST_CHECK rbtree_find( \
        RCPR_SYM(resource)** x, RCPR_SYM(rbtree)* y, const void* z) { \
            return RCPR_SYM(rbtree_find)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK rbtree_delete( \
        RCPR_SYM(resource)** x, RCPR_SYM(rbtree)* y, const void* z) { \
            return RCPR_SYM(rbtree_delete)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK rbtree_clear( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_clear)(x); } \
    static inline void rbtree_swap( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree)* y) { \
            return RCPR_SYM(rbtree_swap)(x,y); } \
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
    static inline RCPR_SYM(rbtree_node)* rbtree_nil_node( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_nil_node)(x); } \
    static inline RCPR_SYM(rbtree_node)* rbtree_root_node( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_root_node)(x); } \
    static inline RCPR_SYM(resource)* rbtree_node_value( \
        RCPR_SYM(rbtree)* x, RCPR_SYM(rbtree_node)* y) { \
            return RCPR_SYM(rbtree_node_value)(x,y); } \
    static inline size_t rbtree_count( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_count)(x); } \
    static inline RCPR_SYM(resource)* rbtree_resource_handle( \
        RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(rbtree_resource_handle)(x); } \
    static inline bool prop_rbtree_valid( \
        const RCPR_SYM(rbtree)* x) { \
            return RCPR_SYM(prop_rbtree_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
