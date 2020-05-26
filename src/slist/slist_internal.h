/**
 * \file slist/slist_internal.h
 *
 * \brief Internal data types and functions for slist.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/slist.h>
#include <rcpr/resource.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct slist
{
    resource hdr;

    MODEL_STRUCT_TAG(slist);

    allocator* alloc;
    slist_node* head;
    slist_node* tail;
    size_t count;
};

struct slist_node
{
    resource hdr;

    MODEL_STRUCT_TAG(slist_node);

    allocator* alloc;
    slist* parent;
    slist_node* next;
    resource* child;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
