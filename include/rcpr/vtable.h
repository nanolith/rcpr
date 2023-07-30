/**
 * \file rcpr/vtable.h
 *
 * \brief Helpers for vtable related mapping.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The RCPR_VTABLE attribute macro is used when specifying that a given
 * vtable data structure should be stored in the rcpr_vtable section of the
 * binary.
 *
 * Since runtime checking of vtable pointers will be enforced in the future,
 * this attribute ensures that the given vtable is in the correct section.
 */
#define RCPR_VTABLE \
    const \
    __attribute__ ((section ("rcpr_vtable")))

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
