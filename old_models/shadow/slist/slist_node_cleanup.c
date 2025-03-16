/**
 * \file models/shadow/slist/slist_node_cleanup.c
 *
 * \brief Shadow method for slist_node_cleanup.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../../../src/slist/slist_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;
RCPR_IMPORT_slist_internal;

status mock_resource_release(resource* r);

/**
 * \brief Clean up an slist node.
 *
 * \param a             Pointer to the slist allocator.
 * \param node          Pointer to the slist_node to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(slist_node_cleanup)(allocator* a, slist_node* node)
{
    RCPR_MODEL_ASSERT(NULL == node->parent && NULL == node->next);

    /* if the child resource is set, release it. */
    if (NULL != node->child)
    {
        mock_resource_release(node->child);
    }

    /* if reclaiming this slist_node instance succeeds, so does this release. */
    return
        allocator_reclaim(a, node);
}
