/**
 * \file examples/mandelbrot/src/config_get_values.c
 *
 * \brief Get the config values.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "config_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/**
 * \brief Get relevant config values.
 *
 * \note The returned filename is owned by the config structure. The caller
 * should not attempt to free it or use it after the config resource is
 * released.
 *
 * \param c                 Pointer to the config instance.
 * \param x                 Pointer to the x coordinate to use to center this
 *                          zoom instance.
 * \param y                 Pointer to the y coordinate to use to center this
 *                          zoom instance.
 * \param width             Width of the image in pixels.
 * \param height            Height of the image in pixels.
 * \param jobs              The number of threads to run in parallel.
 * \param frames            The number of frames to generate.
 * \param filename          Start of the filename.
 *
 * \returns STATUS_SUCCESS on success and a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
config_get_values(
    const config* c, long double* x, long double* y, size_t* width,
    size_t* height, size_t* jobs, size_t* frames, const char** filename)
{
    *x = c->x;
    *y = c->y;
    *width = c->width;
    *height = c->height;
    *jobs = c->jobs;
    *frames = c->frames;
    *filename = c->filename_prefix;

    return STATUS_SUCCESS;
}
