/**
 * \file rcpr/component.h
 *
 * \brief Define components and component families.
 *
 * \copyright 2020-2022 Justin Handville.  Please see license.txt in this
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

    /** \brief Reserved component family. */
    COMPONENT_FAMILY_RESERVED0                                  =         0x06,

    /** \brief Reserved component family. */
    COMPONENT_FAMILY_RESERVED1                                  =         0x07,

    /** \brief Reserved component family. */
    COMPONENT_FAMILY_RESERVED2                                  =         0x08,

    /** \brief Reserved component family. */
    COMPONENT_FAMILY_RESERVED3                                  =         0x09,

    /** \brief Reserved component family. */
    COMPONENT_FAMILY_RESERVED4                                  =         0x0a,

    /** \brief USER0 component family.
     *
     * There are 16 low numbered component families set aside for the user. The
     * upper end is also reserved for users, but these shift based on
     * \ref COMPONENT_FAMILY_LAST. Error codes that require stability, such as
     * those used in APIs, should use families USER0 through USER15.
     */
    COMPONENT_FAMILY_USER0                                      =         0x10,

    /** \brief USER1 component family. */
    COMPONENT_FAMILY_USER1                                      =         0x11,

    /** \brief USER2 component family. */
    COMPONENT_FAMILY_USER2                                      =         0x12,

    /** \brief USER3 component family. */
    COMPONENT_FAMILY_USER3                                      =         0x13,

    /** \brief USER4 component family. */
    COMPONENT_FAMILY_USER4                                      =         0x14,

    /** \brief USER5 component family. */
    COMPONENT_FAMILY_USER5                                      =         0x15,

    /** \brief USER6 component family. */
    COMPONENT_FAMILY_USER6                                      =         0x16,

    /** \brief USER7 component family. */
    COMPONENT_FAMILY_USER7                                      =         0x17,

    /** \brief USER8 component family. */
    COMPONENT_FAMILY_USER8                                      =         0x18,

    /** \brief USER9 component family. */
    COMPONENT_FAMILY_USER9                                      =         0x19,

    /** \brief USER10 component family. */
    COMPONENT_FAMILY_USER10                                      =        0x1a,

    /** \brief USER11 component family. */
    COMPONENT_FAMILY_USER11                                      =        0x1b,

    /** \brief USER12 component family. */
    COMPONENT_FAMILY_USER12                                      =        0x1c,

    /** \brief USER13 component family. */
    COMPONENT_FAMILY_USER13                                      =        0x1d,

    /** \brief USER14 component family. */
    COMPONENT_FAMILY_USER14                                      =        0x1e,

    /** \brief USER15 component family. */
    COMPONENT_FAMILY_USER15                                      =        0x1f,

    /** \brief MAX is the largest component family currently used in this
     * version of RCPR.
     *
     * This ensures that at least one final component family is held in reserve.
     * User code is welcome to use MAX + n where this is < 0xff. However, future
     * releases of RCPR may increase MAX, so any status codes based on these
     * family values would also change.
     *
     * User code needing stable status codes for APIs should use one of the
     * reserved low-end user codes above.
     */
    COMPONENT_FAMILY_MAX
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

    /** \brief uuid library subcomponent scope. */
    RCPR_SUBCOMPONENT_UUID                                  =             0x09,

    /** \brief message discipline subcomponent scope. */
    RCPR_SUBCOMPONENT_MESSAGE                               =             0x0a,

    /** \brief string library subcomponent scope. */
    RCPR_SUBCOMPONENT_STRING                                =             0x0b,

    /** \brief Auto-reset trigger subcomponent scope. */
    RCPR_SUBCOMPONENT_AUTO_RESET_TRIGGER                    =             0x0c,

    /** \brief Condition subcomponent scope. */
    RCPR_SUBCOMPONENT_CONDITION                             =             0x0d,
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

/** \brief Stack library component scope. */
#define RCPR_COMPONENT_STACK \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_STACK)

/** \brief Fiber library component scope. */
#define RCPR_COMPONENT_FIBER \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_FIBER)

/** \brief rbtree library component scope. */
#define RCPR_COMPONENT_RBTREE \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_RBTREE)

/** \brief uuid library component scope. */
#define RCPR_COMPONENT_UUID \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_UUID)

/** \brief message discipline component scope. */
#define RCPR_COMPONENT_MESSAGE \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_MESSAGE)

/** \brief string library component scope. */
#define RCPR_COMPONENT_STRING \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_STRING)

/** \brief auto_reset_trigger component scope. */
#define RCPR_COMPONENT_AUTO_RESET_TRIGGER \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_AUTO_RESET_TRIGGER)

/** \brief condition component scope. */
#define RCPR_COMPONENT_CONDITION \
    COMPONENT_MAKE(COMPONENT_FAMILY_RCPR, RCPR_SUBCOMPONENT_CONDITION)

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
