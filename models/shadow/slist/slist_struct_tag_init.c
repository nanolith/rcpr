/**
 * \file models/shadow/slist/slist_struct_tag_init.c
 *
 * \brief Initialize the slist struct tag.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/slist/slist_internal.h"

int MODEL_STRUCT_TAG_GLOBAL_REF(slist);

void slist_struct_tag_init()
{
    MODEL_STRUCT_TAG_GLOBAL_INIT(slist);
}
