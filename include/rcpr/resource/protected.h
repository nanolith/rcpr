/**
 * \file rcpr/resource/protected.h
 *
 * \brief Protected data types and methods for resource.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
#include <rcpr/model_assert.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward decl for resource_vtable. */
typedef struct RCPR_SYM(resource_vtable) RCPR_SYM(resource_vtable);

struct RCPR_SYM(resource)
{
    const RCPR_SYM(resource_vtable)* vtable;

    RCPR_MODEL_STRUCT_TAG(resource);
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
