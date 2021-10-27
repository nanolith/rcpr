/**
 * \file rcpr/resource/protected.h
 *
 * \brief Protected data types and methods for resource.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
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

    RCPR_MODEL_STRUCT_TAG(resource);
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
