/**
 * \file models/shadow/list/property_list_valid.c
 *
 * \brief Check whether a list instance is valid.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "list_shadow.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(list);

/**
 * \brief Valid \ref list property.
 *
 * \param l             The \ref list instance to be verified.
 *
 * \returns true if the \ref list instance is valid.
 */
bool
RCPR_SYM(property_list_valid)(const RCPR_SYM(list)* l)
{
    RCPR_MODEL_CHECK_OBJECT_READ(l, sizeof(*l));
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        l->RCPR_MODEL_STRUCT_TAG_REF(list), list);

    RCPR_MODEL_ASSERT(prop_resource_valid(&l->hdr));
    RCPR_MODEL_ASSERT(property_allocator_valid(l->alloc));

    if (NULL != l->head)
    {
        RCPR_MODEL_ASSERT(property_list_node_valid(l->head));
        RCPR_MODEL_ASSERT(property_list_node_valid(l->tail));
        RCPR_MODEL_ASSERT(NULL == l->head->prev);
        RCPR_MODEL_ASSERT(NULL == l->tail->next);
    }
    else
    {
        RCPR_MODEL_ASSERT(NULL == l->tail);
    }

    return true;
}
