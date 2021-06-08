/**
 * \file message/message_internal.h
 *
 * \brief Internal data types and functions for the fiber messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/message.h>
#include <rcpr/model_assert.h>
#include <rcpr/rbtree.h>
#include <rcpr/stack.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct message
{
    resource hdr;

    MODEL_STRUCT_TAG(message);

    allocator* alloc;
    mailbox_address returnaddr;
    resource* payload;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
