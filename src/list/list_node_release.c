/**
 * \file list/list_node_release.c
 *
 * \brief Release a \ref list_node instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

/**
 * \brief Release a list_node resource.
 *
 * \param r             Pointer to the list_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status
RCPR_SYM(list_node_release)(
    RCPR_SYM(resource)* r)
{
    list_node* n = (list_node*)r;

    RCPR_MODEL_ASSERT(prop_list_node_valid(n));
    RCPR_MODEL_ASSERT(NULL == n->parent && NULL == n->next);

    /* if the child resource is set, release it. */
    if (NULL != n->child)
    {
        resource* c = n->child;
        n->child = NULL;

        /* ensure that this resource is valid. */
        RCPR_MODEL_ASSERT(prop_resource_valid(c));

        /* release the child resource. */
        status retval = resource_release(c);
        if (STATUS_SUCCESS != retval)
            return retval;
    }

    /* clean up. */
    allocator* a = n->alloc;

    /* if reclaiming this list_node instance succeeds, so does this release. */
    return
        allocator_reclaim(a, n);
}
