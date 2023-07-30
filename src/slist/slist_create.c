/**
 * \file slist/slist_create.c
 *
 * \brief Create a \ref slist instance.
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

/* forward decls. */
static status slist_release(resource*);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(slist);

/* the vtable entry for the slist instance. */
RCPR_VTABLE
resource_vtable slist_vtable = {
    &slist_release };

/**
 * \brief Create a \ref slist instance.
 *
 * \param list          Pointer to the \ref slist pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      slist resource and to allocate new nodes.
 *
 * \note This \ref slist is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref slist_resource_handle on this \ref slist instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p list must not reference a valid list instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p list is set to a pointer to a valid \ref slist
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p list is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(slist_create)(
    RCPR_SYM(slist)** list, RCPR_SYM(allocator)* a)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != list);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));

    /* attempt to allocate memory for this slist. */
    slist* l = NULL;
    int retval =
        allocator_allocate(a, (void**)&l, sizeof(slist));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear structure. */
    memset(l, 0, sizeof(slist));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        l->RCPR_MODEL_STRUCT_TAG_REF(slist), slist);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(l->RCPR_MODEL_STRUCT_TAG_REF(slist), slist);

    /* set the release method. */
    resource_init(&l->hdr, &slist_vtable);

    /* set the allocator. */
    l->alloc = a;

    /* set the head, tail, and count. */
    l->head = NULL;
    l->tail = NULL;
    l->count = 0U;

    /* set the list. */
    *list = l;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_slist_valid(*list));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Release an slist resource.
 *
 * \param r             Pointer to the slist resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
static status slist_release(resource* r)
{
    status retval;
    slist* l = (slist*)r;

    /* iterate through slist nodes, releasing them. */
    while (NULL != l->head)
    {
        slist_node* t = l->head;
        l->head = l->head->next;

        t->parent = NULL;
        t->next = NULL;

        /* clean up the node. */
        retval = slist_node_cleanup(l->alloc, t);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }
    }

    /* clear out tail. */
    l->tail = NULL;

    /* clear out count. */
    l->count = 0U;

    /* clean up. */
    allocator* a = l->alloc;

    /* if reclaiming this slist instance succeeds, so does this release. */
    return
        allocator_reclaim(a, l);
}
