/**
 * \file rcpr/component.h
 *
 * \brief Define components and component families.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief Given a component family and a subcomponent, form a component.
 */
#define COMPONENT_MAKE(family, subcomponent) \
    ((((family) << 8) & 0xFF00) | ((subcomponent) & 0x00FF))

/**
 * \brief Component Family Enumeration.
 */
enum component_family
{
    /** \brief RCPR component family. */
    COMPONENT_FAMILY_RCPR                                       =         0x00,

    /** \brief RCCRYPT component family. */
    COMPONENT_FAMILY_RCCRYPT                                    =         0x01,

    /** \brief RCCERT component family. */
    COMPONENT_FAMILY_RCCERT                                     =         0x02,

    /** \brief RCUOS component family. */
    COMPONENT_FAMILY_RCUOS                                      =         0x03,

    /** \brief RCBLOCK component family. */
    COMPONENT_FAMILY_RCBLOCK                                    =         0x04,

    /** \brief RCBLOCKSVC component family. */
    COMPONENT_FAMILY_RCBLOCKSVC                                 =         0x05,
};

/**
 * \brief RCPR subcomponents.
 */
enum rcpr_subcomponents
{
    /** \brief Global subcomponent scope. */
    RCPR_SUBCOMPONENT_GLOBAL                                =             0x00,

    /** \brief Resource subcomponent scope. */
    RCPR_SUBCOMPONENT_RESOURCE                              =             0x01,

    /** \brief Allocator subcomponent scope. */
    RCPR_SUBCOMPONENT_ALLOCATOR                             =             0x02,

    /** \brief Socket utilitiies subcomponent scope. */
    RCPR_SUBCOMPONENT_SOCKET_UTILITIES                      =             0x03,

    /** \brief Process Socket library subcomponent scope. */
    RCPR_SUBCOMPONENT_PSOCK                                 =             0x04,

    /** \brief Thread library subcomponent scope. */
    RCPR_SUBCOMPONENT_THREAD                                =             0x05,

    /** \brief Stack library subcomponent scope. */
    RCPR_SUBCOMPONENT_STACK                                 =             0x06,

    /** \brief Fiber library subcomponent scope. */
    RCPR_SUBCOMPONENT_FIBER                                 =             0x07,

    /** \brief rbtree library subcomponent scope. */
    RCPR_SUBCOMPONENT_RBTREE                                =             0x08,
};

/** \brief Global component scope. */
#define RCPR_COMPONENT_GLOBAL \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_GLOBAL)

/** \brief Resource component scope. */
#define RCPR_COMPONENT_RESOURCE \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_RESOURCE)

/** \brief Allocator component scope. */
#define RCPR_COMPONENT_ALLOCATOR \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_ALLOCATOR)

/** \brief Socket Utilities component scope. */
#define RCPR_COMPONENT_SOCKET_UTILITIES \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_SOCKET_UTILITIES)

/** \brief Process Socket library component scope. */
#define RCPR_COMPONENT_PSOCK \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_PSOCK)

/** \brief Thread library component scope. */
#define RCPR_COMPONENT_THREAD \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_THREAD)

/** \brief rbtree library component scope. */
#define RCPR_COMPONENT_RBTREE \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_RBTREE)

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
