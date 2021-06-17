/**
 * \file examples/mandelbrot/src/draw_line.c
 *
 * \brief Worker thread entry point.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <stdlib.h>

#include "thread.h"

RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

/**
 * \brief Worker thread entry point.
 *
 * Fetch and draw lines.
 *
 * \param context       The context for this worker thread.
 *
 * \returns a status code indicating success or failure.
 */
status draw_line(void* context)
{
    int retval, release_retval;
    volatile thread_info* info = (volatile thread_info*)context;
    thread_mutex_lock* lock;

    /* acquire the lock. */
    retval = thread_mutex_lock_acquire(&lock, info->mutex);
    if (STATUS_SUCCESS != retval)
    {
        /* something went wrong. Quiesce and return. */
        info->quiesce = true;
        goto done;
    }

    for (;;)
    {
        /* wait on the worker conditional. */
        retval = thread_cond_wait(&lock, info->worker_cond);
        if (STATUS_SUCCESS != retval)
        {
            info->quiesce = true;
            goto cleanup_lock;
        }

        /* if we are quiescing, we're done. */
        if (info->quiesce)
        {
            goto cleanup_lock;
        }

        /* while we aren't done, get a line and start rendering it. */
        while (!info->done)
        {
            size_t line = info->curr_line;

            /* is this a valid line? */
            if (line < info->lines)
            {
                ++info->curr_line;

                /* allocate memory for this line. */
                char* linearr = malloc(info->cols);

                /* release the lock and start rendering. */
                retval =
                    resource_release(thread_mutex_lock_resource_handle(lock));
                if (STATUS_SUCCESS != retval)
                {
                    info->quiesce = true;
                    free(linearr);
                    goto done;
                }

                /* iterate over each pixel. */
                for (size_t i = 0; i < info->cols; ++i)
                {
                    long double x0 = info->startx + (info->scalex * i);
                    long double y0 = info->starty + (info->scaley * line);

                    long double x = 0.0;
                    long double y = 0.0;
                    size_t iteration = 0;
                    const size_t max_iteration = 1000;

                    while (x*x + y*y <= 2*2 && iteration < max_iteration)
                    {
                        long double xtmp = x*x - y*y + x0;
                        y = 2*x*y + y0;
                        x = xtmp;
                        ++iteration;
                    }

                    char ch = 0;
                    if (iteration < max_iteration)
                    {
                        ch = iteration % 256;
                    }

                    linearr[i] = ch;
                }

                /* re-acquire the lock. */
                retval = thread_mutex_lock_acquire(&lock, info->mutex);
                if (STATUS_SUCCESS != retval)
                {
                    /* something went wrong. Quiesce and return. */
                    info->quiesce = true;
                    free(linearr);
                    goto done;
                }

                /* save the line. */
                info->array[line] = linearr;
                ++info->lines_written;

                /* if this is the last line, then signal the main thread. */
                if (info->lines_written == info->lines)
                {
                    info->done = true;

                    /* signal the main thread that we are done. */
                    retval = thread_cond_signal_one(info->main_cond);
                    if (STATUS_SUCCESS != retval)
                    {
                        info->quiesce = true;
                        goto cleanup_lock;
                    }
                }
            }
            else
            {
                info->done = true;
            }
        }
    }

cleanup_lock:
    release_retval = resource_release(thread_mutex_lock_resource_handle(lock));
    if (STATUS_SUCCESS != release_retval)
        if (STATUS_SUCCESS != retval)
            retval = release_retval;

done:
    return retval;
}
