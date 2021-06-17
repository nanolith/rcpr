/**
 * \file slist/slist_node_cleanup.c
 *
 * \brief Clean up (release) a \ref slist_node instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "slist_internal.h"

RCPR_IMPORT_resource;
RCPR_IMPORT_slist;
RCPR_IMPORT_slist_internal;

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
status
RCPR_SYM(slist_node_cleanup)(
    RCPR_SYM(allocator)* a, RCPR_SYM(slist_node)* node)
{
    (void)a;

    return
        slist_node_release((resource*)node);
}
