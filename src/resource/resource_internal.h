/**
 * \file resource/resource_internal.h
 *
 * \brief Internal data types and functions for resource.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/model_assert.h>
#include <rcpr/resource.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(resource)
{
    RCPR_SYM(resource_release_fn) release;

    MODEL_STRUCT_TAG(RCPR_SYM(resource));
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
