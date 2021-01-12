/**
 * \file examples/mandelbrot/src/config_resource_handle.c
 *
 * \brief Get the resource handle for a config instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "config_internal.h"

/**
 * \brief Get the resource handle for this config instance.
 *
 * \param c                 Pointer to the config instance.
 *
 * \returns the resource handle for this config instance.
 */
resource* config_resource_handle(config* c)
{
    return &(c->hdr);
}
