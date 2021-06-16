/**
 * \file examples/mandelbrot/src/main.c
 *
 * \brief Main entry point for the Mandelbrot zoom example.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <math.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "config.h"
#include "thread.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/**
 * \brief Main entry point for the mandelbrot example.
 */
int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    status retval;
    config* c = NULL;
    int errorcode = 0;
    long double x;
    long double y;
    size_t width;
    size_t height;
    size_t jobs;
    size_t frames;
    const char* filename_prefix;
    thread** threads = NULL;
    thread_info info;
    thread_mutex_lock* lock;
    char filename[1024];

    /* create a malloc allocator. */
    retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 1;
        goto done;
    }

    /* read the config from the commandline. */
    retval = config_create(&c, alloc, argc, argv);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 2;
        goto cleanup_allocator;
    }

    /* get x, y, number of jobs, and filename. */
    retval =
        config_get_values(
            c, &x, &y, &width, &height, &jobs, &frames, &filename_prefix);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 3;
        goto cleanup_config;
    }

    /* clear thread_info. */
    memset(&info, 0, sizeof(info));

    /* allocate memory for the array. */
    info.array = (char**)malloc(height * sizeof(char*));
    if (NULL == info.array)
    {
        errorcode = 4;
        goto cleanup_config;
    }

    /* set done to true so the threads wait on the conditional. */
    info.done = true;

    /* create the mutex. */
    retval = thread_mutex_create(&info.mutex, alloc);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 5;
        goto free_array;
    }

    /* create the worker thread conditional. */
    retval = thread_cond_create(&info.worker_cond, alloc);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 6;
        goto release_mutex;
    }
    
    /* create the main thread conditional. */
    retval = thread_cond_create(&info.main_cond, alloc);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 7;
        goto release_worker_cond;
    }

    /* create the thread array. */
    threads = (thread**)malloc(jobs * sizeof(thread*));
    if (NULL == threads)
    {
        errorcode = 8;
        goto release_main_cond;
    }

    /* clear the thread array. */
    memset(threads, 0, jobs * sizeof(thread*));

    /* create each thread. They will immediately block on the worker cond.*/
    for (size_t i = 0; i < jobs; ++i)
    {
        retval = thread_create(&threads[i], alloc, 16384, &info, draw_line);
        if (STATUS_SUCCESS != retval)
        {
            errorcode = 9;
            goto cleanup_threads;
        }
    }

    /* We need to compute the initial scale and starting x / y positions. */
    long double xstart = -2.5 + x;
    long double xend = 1.0 + x;
    long double ystart = -1.0 + y;
    long double yend = 1.0 + y;
    long double xfactor = xend - xstart;
    xfactor /= (long double)width;
    xfactor = fabsl(xfactor);
    long double yfactor = yend - ystart;
    yfactor /= (long double)height;
    yfactor = fabsl(yfactor);
    info.scalex = xfactor;
    info.scaley = yfactor;
    info.startx = xstart;
    info.starty = ystart;
    info.lines = height;
    info.cols = width;

    /* we want to zoom in 5% each frame. */
    long double zoom_factor = 1.0 - 0.05;
    long double startcenterx = (xfactor*((long double)width) / 2.0) + xstart;
    long double startcentery = (yfactor*((long double)height) / 2.0) + ystart;
    long double endcenterx = x;
    long double endcentery = y;
    long double translatex = (endcenterx - startcenterx) / 30.0;
    long double translatey = (endcentery - startcentery) / 30.0;
    long double translatefactor = 0.05;
    size_t translations = 0;
    long double zoom = zoom_factor;

    /* get the lock. */
    retval = thread_mutex_lock_acquire(&lock, info.mutex);
    if (STATUS_SUCCESS != retval)
    {
        errorcode = 11;
        goto cleanup_threads;
    }

    /* start our loop. */
    for (size_t i = 0; i < frames; ++i)
    {
        /* set done to false to start the threads. */
        info.done = false;
        /* start on the first line. */
        info.curr_line = 0;
        info.lines_written = 0;

        /* wake up the threads. */
        retval = thread_cond_signal_all(info.worker_cond);
        if (STATUS_SUCCESS != retval)
        {
            errorcode = 10;
            goto cleanup_threads;
        }

        /* wait on the main cond, which will trip once the frame is done. */
        retval = thread_cond_wait(&lock, info.main_cond);
        if (STATUS_SUCCESS != retval)
        {
            errorcode = 12;
            goto cleanup_threads;
        }

        printf("Frame %d complete.\n", i);

        /* write the frame to file. */
        snprintf(
            filename, sizeof(filename), "%s%010lu.pgm", filename_prefix, i);
        printf("Creating %s\n", filename);
        FILE* fp = fopen(filename, "w");
        fprintf(fp, "P3\n%lu %lu\n255\n", width, height);
        for (size_t j = 0; j < info.lines; ++j)
        {
            if (NULL != info.array[j])
            {
                for (size_t k = 0; k < info.cols; ++k)
                {
                    fprintf(fp, "0 0 %u ", info.array[j][k]);
                }

                fprintf(fp, "\n");
            }
            else
            {
                printf("Skipping missing line %u\n", j);
            }
        }
        fclose(fp);

        /* free the frame. */
        for (size_t j = 0; j < info.lines; ++j)
        {
            if (NULL != info.array[j])
                free(info.array[j]);
            info.array[j] = NULL;
        }

        /* do the zoom. */
        xstart = -2.5*zoom + x;
        xend = 1.0*zoom + x;
        ystart = -1.0*zoom + y;
        yend = 1.0*zoom + y;
        xfactor = xend - xstart;
        xfactor /= (long double)width;
        xfactor = fabsl(xfactor);
        yfactor = yend - ystart;
        yfactor /= (long double)height;
        yfactor = fabsl(yfactor);
        info.scalex = xfactor;
        info.scaley = yfactor;
        info.startx = xstart;
        info.starty = ystart;
        zoom *= zoom_factor;
    }

    /* success. */
    errorcode = 0;
    goto cleanup_config;

cleanup_lock:
    if (STATUS_SUCCESS !=
            resource_release(thread_mutex_lock_resource_handle(lock)))
    if (0 == errorcode)
        errorcode = 97;

cleanup_threads:
    /* this code wakes up threads and ends the process if we can't. */
    /* We can't simulate in CBMC yet. */
    #ifndef CBMC
    info.quiesce = true;
    if (STATUS_SUCCESS != thread_cond_signal_all(info.worker_cond))
    {
        if (0 == errorcode)
            errorcode = 96;

        /* we can't do any further cleanup if this happens. */
        exit(errorcode);
    }
    #endif

    for (size_t i = 0; i < jobs; ++i)
    {
        if (STATUS_SUCCESS !=
                resource_release(thread_resource_handle(threads[i])))
            if (0 == errorcode)
                errorcode = 95;
    }

    free(threads);

release_main_cond:
    if (STATUS_SUCCESS !=
            resource_release(thread_cond_resource_handle(info.main_cond)))
        if (0 == errorcode)
            errorcode = 94;

release_worker_cond:
    if (STATUS_SUCCESS !=
            resource_release(thread_cond_resource_handle(info.worker_cond)))
        if (0 == errorcode)
            errorcode = 93;

release_mutex:
    if (STATUS_SUCCESS !=
            resource_release(thread_mutex_resource_handle(info.mutex)))
        if (0 == errorcode)
            errorcode = 92;

free_array:
    free(info.array);

cleanup_config:
    if (STATUS_SUCCESS != resource_release(config_resource_handle(c)))
        if (0 == errorcode)
            errorcode = 91;

cleanup_allocator:
    if (STATUS_SUCCESS != resource_release(allocator_resource_handle(alloc)))
        if (0 == errorcode)
            errorcode = 90;

done:
    return errorcode;
}
