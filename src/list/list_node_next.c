/**
 * \file slist/list_node_next.c
 *
 * \brief Get the next node for this \ref list_node instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list_internal.h"

/**
 * \brief Given an \ref list_node, return the next \ref list_node in the list.
 *
 * \param next          Pointer to the \ref list_node pointer to receive the
 *                      next value.
 * \param node          Pointer to the \ref list_node under query.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p next must not reference a valid \ref list_node instance and must
 *        be NULL.
 *      - \p node must reference a valid \ref list_node and must not be NULL.
 *
 * \post
 *      - On success, \p next is set to the next node in this list, or NULL if
 *        \p node is the tail of the list.
 *      - On failure, \p next is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_node_next)(
    RCPR_SYM(list_node)** next, RCPR_SYM(list_node)* node)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != next);
    RCPR_MODEL_ASSERT(prop_slist_node_valid(node));

    /* set the next node. */
    *next = node->next;

    return STATUS_SUCCESS;
}
