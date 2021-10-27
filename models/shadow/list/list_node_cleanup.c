/**
 * \file models/shadow/list/list_node_cleanup.c
 *
 * \brief Shadow method for list_node_cleanup.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../../../src/list/list_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;
RCPR_IMPORT_resource;

status mock_resource_release(resource* r);

/**
 * \brief Clean up a list node.
 *
 * \param a             Pointer to the list allocator.
 * \param node          Pointer to the list_node to be released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(list_node_cleanup)(allocator* a, list_node* node)
{
    RCPR_MODEL_ASSERT(NULL == node->parent && NULL == node->next);

    /* if the child resource is set, release it. */
    if (NULL != node->child)
    {
        mock_resource_release(node->child);
    }

    /* if reclaiming this list_node instance succeeds, so does this release. */
    return
        allocator_reclaim(a, node);
}
