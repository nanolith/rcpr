#pragma once

struct pthread_attr
{
};

struct pthread
{
};

struct pthread_mutex_lock
{
};

struct pthread_mutex
{
    struct pthread_mutex_lock* lock;
};

struct pthread_cond
{
};
