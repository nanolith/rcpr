/**
 * \file models/shadow/bigint/bigint_struct_tag_init.c
 *
 * \brief Initialize the bigint struct tag.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/bigint/bigint_internal.h"

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(bigint);

void bigint_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(bigint);
}
