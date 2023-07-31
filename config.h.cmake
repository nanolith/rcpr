/**
 * \file rcpr/config.h
 *
 * \brief Generated configuration file data for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#define MAKE_C_VERSION(X,Y) V ## X ## _ ## Y
#define RCPR_VERSION_SYM \
    MAKE_C_VERSION(@RCPR_VERSION_MAJOR@, @RCPR_VERSION_MINOR@)

#define RCPR_VERSION_STRING \
    "@RCPR_VERSION_MAJOR@.@RCPR_VERSION_MINOR@.@RCPR_VERSION_REL@"

#cmakedefine RCPR_VTABLE_RUNTIME_ENFORCEMENT
