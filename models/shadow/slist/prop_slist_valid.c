/**
 * \file models/shadow/psock/prop_slist_valid.c
 *
 * \brief Check whether an slist instance is valid.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/slist/slist_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(slist);

/**
 * \brief Valid \ref slist property.
 *
 * \param list           The \ref slist instance to be verified.
 *
 * \returns true if the \ref slist instance is valid.
 */
bool prop_slist_valid(const slist* list)
{
    MODEL_ASSERT(NULL != list);
    MODEL_ASSERT_STRUCT_TAG_INITIALIZED(
        list->MODEL_STRUCT_TAG_REF(slist), slist);

    return
        prop_resource_valid(&list->hdr)
     && prop_allocator_valid(list->alloc)
     && (    (list->count > 0 && list->head != NULL && list->tail != NULL)
          || (list->count == 0 && list->head == NULL && list->tail == NULL));
}
