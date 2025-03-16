/**
 * \file models/shadow/list/list_node_release.c
 *
 * \brief Shadow method for list_node_release.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../../../src/allocator/allocator_internal.h"
#include "../../../src/list/list_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;
RCPR_IMPORT_resource;

status mock_resource_release(resource* r);

/**
 * \brief Release an list_node resource.
 *
 * \param r             Pointer to the list_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(list_node_release)(resource* r)
{
    list_node* n = (list_node*)r;

    RCPR_MODEL_ASSERT(prop_list_node_valid(n));
    RCPR_MODEL_ASSERT(NULL == n->parent && NULL == n->next);

    /* if the child resource is set, release it. */
    if (NULL != n->child)
    {
        mock_resource_release(n->child);
    }

    /* clean up. */
    allocator* a = n->alloc;

    /* if reclaiming this list_node instance succeeds, so does this release. */
    return
        allocator_reclaim(a, n);
}
