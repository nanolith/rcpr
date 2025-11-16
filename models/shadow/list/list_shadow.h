/**
 * \file rcpr/models/shadow/list/list_shadow.h
 *
 * \brief Shadow header for RCPR list.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/list.h>

struct RCPR_SYM(list)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(list);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(list_node)* head;
    RCPR_SYM(list_node)* tail;
    size_t count;
};

struct RCPR_SYM(list_node)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(list_node);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(list)* parent;
    RCPR_SYM(list_node)* prev;
    RCPR_SYM(list_node)* next;
    RCPR_SYM(resource)* child;
};
