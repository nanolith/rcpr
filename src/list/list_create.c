/**
 * \file list/list_create.c
 *
 * \brief Create a \ref list instance.
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

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;
RCPR_IMPORT_resource;

/* forward decls. */
static status list_release(resource*);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(list);

/* the vtable entry for the list instance. */
RCPR_VTABLE
resource_vtable list_vtable = {
    &list_release };

/**
 * \brief Create a \ref list instance.
 *
 * \param l             Pointer to the \ref list pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      list resource and to allocate new nodes.
 *
 * \note This \ref list is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref list_resource_handle on this \ref list instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p l must not reference a valid list instance and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p l is set to a pointer to a valid \ref list
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p l is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_create)(
    RCPR_SYM(list)** l, RCPR_SYM(allocator)* a)
{
    status retval;

    /* function contract preconditions. */
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(list_create), l, a);

    /* attempt to allocate memory for this list. */
    list* tmp = NULL;
    retval = allocator_allocate(a, (void**)&tmp, sizeof(list));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(list));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(list), list);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(tmp->RCPR_MODEL_STRUCT_TAG_REF(list), list);

    /* set the release method. */
    resource_init(&tmp->hdr, &list_vtable);

    /* set the allocator. */
    tmp->alloc = a;

    /* set the head, tail, and count. */
    tmp->head = NULL;
    tmp->tail = NULL;
    tmp->count = 0U;

    /* set the list. */
    *l = tmp;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(property_list_valid(*l));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    /* check postconditions. */
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(list_create), retval, l, a);

    return retval;
}

/**
 * \brief Release an list resource.
 *
 * \param r             Pointer to the list resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
static status list_release(resource* r)
{
    status retval;
    list* l = (list*)r;

    /* clear list. */
    retval = list_clear(l);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clean up. */
    allocator* a = l->alloc;

    /* if reclaiming this list instance succeeds, so does this release. */
    return
        allocator_reclaim(a, l);
}
