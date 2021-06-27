/**
 * \file slist/list_node_prev.c
 *
 * \brief Get the previous node for this \ref list_node instance.
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
 * \brief Given an \ref list_node, return the previous \ref list_node in the
 * list.
 *
 * \param prev          Pointer to the \ref list_node pointer to receive the
 *                      previous value.
 * \param node          Pointer to the \ref list_node under query.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p prev must not reference a valid \ref list_node instance and must
 *        be NULL.
 *      - \p node must reference a valid \ref list_node and must not be NULL.
 *
 * \post
 *      - On success, \p prev is set to the previous node in this list, or NULL
 *        if \p node is the head of the list.
 *      - On failure, \p prev is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_node_prev)(
    RCPR_SYM(list_node)** prev, RCPR_SYM(list_node)* node)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != prev);
    RCPR_MODEL_ASSERT(prop_slist_node_valid(node));

    /* set the prev node. */
    *prev = node->prev;

    return STATUS_SUCCESS;
}
