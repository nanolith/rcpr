#!/bin/sh

if [ "$1" == "ld" ]; then
    USE_LINKER=cc
elif [ "$1" == "goto-ld" ]; then
    USE_LINKER=goto-cc
else
    USE_LINKER=cc
fi

shift

$USE_LINKER $*
