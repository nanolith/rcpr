/**
 * \file list/list_head.c
 *
 * \brief Get the head node for this \ref list instance.
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

/**
 * \brief Get the head of a \ref list.
 *
 * \param node          Pointer to the \ref list_node pointer to receive this
 *                      resource on success.
 * \param l             Pointer to the \ref list under query.
 *
 * \note This \ref list_node is owned by the \ref list queried.  To take
 * ownership of this \ref list_node, the caller must call \ref list_remove to
 * remove this \ref list_node from the \ref list.  However, it is possible to
 * change the \ref resource owned by this \ref list_node without first removing
 * it from the \ref list by calling \ref list_node_child_swap.
 *
 * If there is a head node, it is populated in \p node.  However, if this list
 * is empty, then \p node is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p node must not reference a valid \ref list_node instance and must
 *        not be NULL.
 *      - \p l must reference a valid \ref list and must not be NULL.
 *
 * \post
 *      - On success, \p node is set to the head of the \ref list, which can be
 *        NULL if \p l is empty.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_head)(
    RCPR_SYM(list_node)** node, RCPR_SYM(list)* l)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != node);
    RCPR_MODEL_ASSERT(prop_list_valid(l));

    /* set the node to head. */
    *node = l->head;

    return STATUS_SUCCESS;
}
