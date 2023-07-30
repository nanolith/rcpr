/**
 * \file slist/slist_node_create.c
 *
 * \brief Create a \ref slist_node instance.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "slist_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;
RCPR_IMPORT_slist_internal;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(slist_node);

/* the vtable entry for the slist node instance. */
RCPR_VTABLE
resource_vtable slist_node_vtable = {
    &slist_node_release };

/**
 * \brief Create a \ref slist_node instance.
 *
 * \param node          Pointer to the \ref slist_node pointer to receive this
 *                      resource on success.
 * \param list          Pointer to the parent \ref slist instance.
 * \param r             Pointer to the child \ref resource instance.
 *
 * \note This \ref slist_node is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * slist_node_resource_handle on this \ref slist_node instance.  If \p r is not
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
 *      - \p list must reference a valid list instance.
 *      - \p r must either reference a valid resource instance or be NULL.
 *
 * \post
 *      - On success, \p node is set to a pointer to a valid \ref slist_node
 *        instance, which is a \ref resource owned by the \p list.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_node_create)(
    RCPR_SYM(slist_node)** node, RCPR_SYM(slist)* list, RCPR_SYM(resource)* r)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != node);
    RCPR_MODEL_ASSERT(prop_slist_valid(list));
    RCPR_MODEL_ASSERT(NULL == r || prop_resource_valid(r));

    /* attempt to allocate memory for this slist_node. */
    slist_node* n = NULL;
    int retval =
        allocator_allocate(list->alloc, (void**)&n, sizeof(slist_node));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear structure. */
    memset(n, 0, sizeof(slist_node));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        n->RCPR_MODEL_STRUCT_TAG_REF(slist_node), slist_node);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        n->RCPR_MODEL_STRUCT_TAG_REF(slist_node), slist_node);

    /* set the release method. */
    resource_init(&n->hdr, &slist_node_vtable);

    /* set the allocator. */
    n->alloc = list->alloc;

    /* set the child. */
    n->child = r;

    /* set parent to NULL. */
    n->parent = NULL;

    /*set next to NULL. */
    n->next = NULL;

    /* set the node. */
    *node = n;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_slist_node_valid(*node));

    /* set the parent; this breaks our invariant, but the caller fixes it up. */
    n->parent = list;

    /* success. */
    return STATUS_SUCCESS;
}
