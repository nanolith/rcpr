/**
 * \file examples/mandelbrot/src/config_create.c
 *
 * \brief Create a config instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <stdlib.h>
#include <string.h>

#include "config_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/* forward decls. */
static status config_resource_release(resource* r);
static void config_set_defaults(config* c);

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
    config** c, allocator* a, int argc, char* argv[])
{
    status retval;
    config* tmp;

    /* create the structure. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(config));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(config));

    /* set the resource release method. */
    resource_init(&tmp->hdr, &config_resource_release);

    /* set the defaults. */
    config_set_defaults(tmp);

    /* return this instance to the caller. */
    *c = tmp;

    /* success. */
    retval = STATUS_SUCCESS;

done:
    return retval;
}

/**
 * \brief Set the defaults for a config instance.
 *
 * \param c             The config instance to set.
 */
static void config_set_defaults(config* c)
{
    /* render this zoom location by default. */
    c->x = 0.013438870532012129028364919004019686867528573314565492885548699;
    c->y = 0.655614218769465062251320027664617466691295975864786403994151735;

    /* render at 1080p by default. */
    c->width = 1920;
    c->height = 1080;

    /* run eight concurrent jobs by default. */
    c->jobs = 8;

    /* build 18000 frames (300 seconds at 60 fps). */
    c->frames = 18000;

    /* set a reasonable filename. */
    c->filename_prefix = strdup("mandelzoom_");
}

/**
 * \brief Release a config resource.
 *
 * \param r             The config resource to release.
 *
 * \returns STATUS_SUCCESS on success and a non-zero error code on failure.
 */
static status config_resource_release(resource* r)
{
    config* c = (config*)r;

    /* if the filename prefix is set, free it. */
    if (NULL != c->filename_prefix)
        free(c->filename_prefix);

    /* clear the structure. */
    memset(c, 0, sizeof(config));

    return STATUS_SUCCESS;
}
