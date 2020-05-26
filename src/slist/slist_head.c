/**
 * \file slist/slist_head.c
 *
 * \brief Get the head node for this \ref slist instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "slist_internal.h"

/**
 * \brief Get the head of a \ref slist.
 *
 * \param node          Pointer to the \ref slist_node pointer to receive this
 *                      resource on success.
 * \param list          Pointer to the \ref slist under query.
 *
 * \note This \ref slist_node is owned by the \ref slist queried.  To take
 * ownership of this \ref slist_node, the caller must call \ref slist_remove to
 * remove this \ref slist_node from the \ref slist.  However, it is possible to
 * change the \ref resource owned by this \ref slist_node without first removing
 * it from the \ref slist by calling \ref slist_node_child_swap.
 *
 * If there is a head node, it is populated in \p node.  However, if this list
 * is empty, then \p node is set to NULL.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *
 * \pre
 *      - \p node must not reference a valid \ref slist_node instance and must
 *        not be NULL.
 *      - \p slist must reference a valid \ref slist and must not be NULL.
 *
 * \post
 *      - On success, \p node is set to the head of the \ref slist, which can be
 *        NULL if \p list is empty.
 *      - On failure, \p node is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
slist_head(
    slist_node** node, slist* list)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != node);
    MODEL_ASSERT(NULL == *node);
    MODEL_ASSERT(prop_slist_valid(list));

    /* set the node to head. */
    *node = list->head;

    return STATUS_SUCCESS;
}
