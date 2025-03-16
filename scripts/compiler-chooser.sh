#!/bin/sh

if [ "$1" == "cc" ]; then
    USE_COMPILER=cc
    EXTRA_FLAGS=
elif [ "$1" == "goto-cc" ]; then
    USE_COMPILER=goto-cc
    EXTRA_FLAGS=-DCBMC
else
    USE_COMPILER=cc
    EXTRA_FLAGS=
fi

shift

$USE_COMPILER $EXTRA_FLAGS $*
