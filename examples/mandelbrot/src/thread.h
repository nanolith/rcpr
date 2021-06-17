/**
 * \file examples/mandelbrot/src/thread.h
 *
 * \brief Worker thread structure.
 */

#include <rcpr/thread.h>

#pragma once

/* forward decls. */
typedef struct thread_info thread_info;

struct thread_info
{
    RCPR_SYM(thread_mutex)* mutex;
    RCPR_SYM(thread_cond)* worker_cond;
    RCPR_SYM(thread_cond)* main_cond;

    size_t curr_line;
    size_t lines_written;
    volatile bool quiesce;
    bool done;
    size_t cols;
    size_t lines;
    long double scalex;
    long double scaley;
    long double startx;
    long double starty;

    char** array;
};

/**
 * \brief Worker thread entry point.
 *
 * Fetch and draw lines.
 *
 * \param context       The context for this worker thread.
 *
 * \returns a status code indicating success or failure.
 */
status draw_line(void* context);
