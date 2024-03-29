/**
 * \file list/list_node_create.c
 *
 * \brief Create a \ref list_node instance.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(list_node);

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;
RCPR_IMPORT_resource;

/* the vtable entry for the list node instance. */
RCPR_VTABLE
resource_vtable list_node_vtable = {
    &list_node_release };

/**
 * \brief Create a \ref list_node instance.
 *
 * \param node          Pointer to the \ref list_node pointer to receive this
 *                      resource on success.
 * \param l             Pointer to the parent \ref list instance.
 * \param r             Pointer to the child \ref resource instance.
 *
 * \note This \ref list_node is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * list_node_resource_handle on this \ref list_node instance.  If \p r is not
 * NULL, then it must be a valid \ref reference instance.  The node takes
 * ownership of this reference.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p node must not reference a valid list node instance and must not be
 *        NULL.
 *      - \p l must reference a valid list instance.
 *      - \p r must either reference a valid resource instance or be NULL.
 *
 * \post
 *      - On success, \p node is set to a pointer to a valid \ref list_node
 *        instance, which is a \ref resource owned by \p l.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_node_create)(
    RCPR_SYM(list_node)** node, RCPR_SYM(list)* l, RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != node);
    RCPR_MODEL_ASSERT(prop_list_valid(l));
    RCPR_MODEL_ASSERT(NULL == r || prop_resource_valid(r));

    /* attempt to allocate memory for this list_node. */
    list_node* n = NULL;
    int retval =
        allocator_allocate(l->alloc, (void**)&n, sizeof(list_node));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear structure. */
    memset(n, 0, sizeof(list_node));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        n->RCPR_MODEL_STRUCT_TAG_REF(list_node), list_node);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        n->RCPR_MODEL_STRUCT_TAG_REF(list_node), list_node);

    /* set the release method. */
    resource_init(&n->hdr, &list_node_vtable);

    /* set the allocator. */
    n->alloc = l->alloc;

    /* set the child. */
    n->child = r;

    /* set parent to NULL. */
    n->parent = NULL;

    /* set next to NULL. */
    n->next = NULL;

    /* set prev to NULL. */
    n->prev = NULL;

    /* set the node. */
    *node = n;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_list_node_valid(*node));

    /* set the parent; this breaks our invariant, but the caller fixes it up. */
    n->parent = l;

    /* success. */
    return STATUS_SUCCESS;
}
