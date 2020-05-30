/**
 * \file models/shadow/slist/slist_node_release.c
 *
 * \brief Shadow method for slist_node_release.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../../../src/allocator/allocator_internal.h"
#include "../../../src/slist/slist_internal.h"

status mock_resource_release(resource* r);

/**
 * \brief Release an slist_node resource.
 *
 * \param r             Pointer to the slist_node resource to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status slist_node_release(resource* r)
{
    slist_node* n = (slist_node*)r;

    MODEL_ASSERT(prop_slist_node_valid(n));
    MODEL_ASSERT(NULL == n->parent && NULL == n->next);

    /* if the child resource is set, release it. */
    if (NULL != n->child)
    {
        mock_resource_release(n->child);
    }

    /* clean up. */
    allocator* a = n->alloc;

    /* if reclaiming this slist_node instance succeeds, so does this release. */
    return
        allocator_reclaim(a, n);
}
