/**
 * \file list/list_node_cleanup.c
 *
 * \brief Clean up (release) a \ref list_node instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;
RCPR_IMPORT_resource;

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
status
RCPR_SYM(list_node_cleanup)(
    RCPR_SYM(allocator)* a, RCPR_SYM(list_node)* node)
{
    (void)a;

    return
        list_node_release((resource*)node);
}
