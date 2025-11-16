/**
 * \file list/list_clear.c
 *
 * \brief Clear a \ref list instance.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "list_internal.h"

RCPR_IMPORT_list;
RCPR_IMPORT_list_internal;

/**
 * \brief Clear a list instance, removing all nodes and their resources.
 *
 * \param l             The list to clear.
 *
 * \pre
 *      - \p l must point to a valid \ref list instance.
 * \post
 *      - On success, \p l points to a valid \ref slist instance that has zero
 *        nodes.
 *      - On failure, \p l may still contain some nodes.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(list_clear)(RCPR_SYM(list)* l)
{
    status retval;

    /* check preconditions. */
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(RCPR_SYM(list_clear), l);

    /* iterate through list nodes, releasing them. */
    while (NULL != l->head)
    {
        list_node* t = l->head;
        l->head = l->head->next;
        l->count -= 1U;

        t->parent = NULL;
        t->next = NULL;
        t->prev = NULL;

        /* clean up node. */
        retval = list_node_cleanup(l->alloc, t);
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }
    }

    /* tail is now NULL. */
    l->tail = NULL;

    /* count is now 0. */
    l->count = 0U;

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    /* check postconditions. */
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(RCPR_SYM(list_clear), retval, l);

    return retval;
}
