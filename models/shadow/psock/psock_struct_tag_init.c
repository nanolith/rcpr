/**
 * \file models/shadow/psock/psock_struct_tag_init.c
 *
 * \brief Initialize the psock struct tag.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../../src/psock/psock_internal.h"

int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(psock);

void psock_struct_tag_init()
{
    RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(psock);
}
