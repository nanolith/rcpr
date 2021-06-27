/**
 * \file queue/queue_internal.h
 *
 * \brief Internal data types and functions for queue.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/model_assert.h>
#include <rcpr/queue.h>

#include "../slist/slist_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(queue)
{
    RCPR_SYM(resource) hdr;
    RCPR_SYM(slist)* list;

    RCPR_MODEL_STRUCT_TAG(queue);
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
