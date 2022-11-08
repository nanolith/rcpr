#pragma once

struct pthread_attr
{
};

typedef struct dummy_pthread_attr dummy_pthread_attr;

struct dummy_pthread_attr
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

typedef struct dummy_pthread_cond dummy_pthread_cond;

struct dummy_pthread_cond
{
};
