/**
 * \file models/shadow/list/prop_list_valid.c
 *
 * \brief Check whether a list instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/list/list_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(list);

/**
 * \brief Valid \ref list property.
 *
 * \param list           The \ref list instance to be verified.
 *
 * \returns true if the \ref list instance is valid.
 */
bool RCPR_SYM(prop_list_valid)(const list* l)
{
    RCPR_MODEL_ASSERT(NULL != l);
    RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        l->RCPR_MODEL_STRUCT_TAG_REF(list), list);

    return
        prop_resource_valid(&l->hdr)
     && prop_allocator_valid(l->alloc)
     && (    (l->count > 0 && l->head != NULL && l->tail != NULL)
          || (l->count == 0 && l->head == NULL && l->tail == NULL));
}
