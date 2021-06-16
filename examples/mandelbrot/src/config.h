/**
 * \file examples/mandelbrot/src/config.h
 *
 * \brief Config declarations.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward declarations. */
typedef struct config config;

/**
 * \brief Read the configuration from the command-line.
 *
 * \param c                 Pointer to the pointer to receive the \ref config.
 * \param a                 Allocator to use when creating config.
 * \param argc              The number of arguments.
 * \param argv              The argument vector.
 *
 * \note On success, this creates a \ref config instance which is owned by the
 * caller and must be released by calling \ref resource_release on its resource
 * handle.
 *
 * \returns STATUS_SUCCESS on success and a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
config_create(
    config** c, RCPR_SYM(allocator)* a, int argc, char* argv[]);

/**
 * \brief Get the resource handle for this config instance.
 *
 * \param c                 Pointer to the config instance.
 *
 * \returns the resource handle for this config instance.
 */
RCPR_SYM(resource)* config_resource_handle(config* c);

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
    size_t* height, size_t* jobs, size_t* frames, const char** filename);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
