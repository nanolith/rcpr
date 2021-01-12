/**
 * \file examples/mandelbrot/src/config.h
 *
 * \brief Definitions for the config struct.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/resource.h>

#include "config.h"
#include "../../../src/resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief Configuration for Mandelbrot zoom.
 */
struct config
{
    /** \brief this is a resource. */
    resource hdr;

    /** \brief the zoom X coordinate. */
    long double x;

    /** \brief the zoom Y coordinate. */
    long double y;

    /** \brief the width of each frame. */
    size_t width;

    /** \brief the height of each frame. */
    size_t height;

    /** \brief the number of threads to run concurrently. */
    size_t jobs;

    /** \brief the number of frames to create. */
    size_t frames;

    /** \brief the filename prefix in which zoom frames should be stored. */
    char* filename_prefix;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
