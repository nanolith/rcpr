##
# \file fiber/platform/sysv/x86_64/fiber_switch.s
#
# \brief Switch between two fibers.
#
# \copyright 2021 Justin Handville.  Please see license.txt in this
# distribution for the license terms under which this software is distributed.

# This implementation was adapted from Boost::Context.  Here is the relevant
# copyright information for that library:
# Copyright Oliver Kowalke 2009.
# Distributed under the Boost Software License, Version 1.0.
# (See contrib/boost_license_1_0.txt or http://www.boost.org/LICENSE_1_0.txt)

# Modifications Copyright 2021 Justin Handville. Please see license.txt in this
# distribution for the license terms under which these modifications are
# distributed.

.include "fiber_struct.inc"

#fiber switch function
.section text
.globl rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_2_fiber_switch
.type fiber_switch,@function

# -----------------------------------------------------------------
# |   0   |   1   |   2   |   3   |   4   |   5   |   6   |   7   |
# -----------------------------------------------------------------
# |  0x0  |  0x4  |  0x8  |  0xc  |  0x10 |  0x14 |  0x18 |  0x1c |
# -----------------------------------------------------------------
# |fcmxcsr|fcx87cw|      R12      |      R13      |      R14      |
# -----------------------------------------------------------------
# -----------------------------------------------------------------
# |   8   |   9   |  10   |  11   |   12  |   13  |   14  |   15  |
# -----------------------------------------------------------------
# |  0x20 |  0x24 |  0x28 |  0x2c |  0x30 |  0x34 |  0x38 |  0x3c |
# -----------------------------------------------------------------
# |      R15      |      RBX      |      RBP      |      RIP      |
# -----------------------------------------------------------------

#switch takes five arguments: the previous fiber, the new fiber, the restore
#discipline id, the restore reason code, and the restore parameter pointer.

.text
.align 16
rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_2_fiber_switch:

    #compute space for spilling to the stack
    leaq -0x38(%rsp), %rsp

    #save the MMX control register.
    stmxcsr  (%rsp)
    #save the x87 control word.
    fnstcw   0x4(%rsp)

    #save R12.
    movq  %r12, 0x8(%rsp)
    #save R13.
    movq  %r13, 0x10(%rsp)
    #save R14.
    movq  %r14, 0x18(%rsp)
    #save R15.
    movq  %r15, 0x20(%rsp)
    #save RBX.
    movq  %rbx, 0x28(%rsp)
    #save RBP.
    movq  %rbp, 0x30(%rsp)

    #save the updated stack pointer in the previous fiber
    movq %rsp, fiber_stack_ptr(%rdi)

    # restore the stack pointer from the new fiber
    movq fiber_stack_ptr(%rsi), %rsp

    # get the return address
    movq 0x38(%rsp), %r9

    #restore the MMX control register
    ldmxcsr  (%rsp)
    #restore the x87 control word
    fldcw    0x4(%rsp)

    #restore R12.
    movq  0x8(%rsp), %r12
    #restore R13.
    movq  0x10(%rsp), %r13
    #restore R14.
    movq  0x18(%rsp), %r14
    #restore R15.
    movq  0x20(%rsp), %r15
    #restore RBX.
    movq  0x28(%rsp), %rbx
    #restore RBP.
    movq  0x30(%rsp), %rbp

    #set the restore discipline id pointer (parameter 3).
    movq %rdx, fiber_restore_discipline_id(%rsi)
    #set the restore reason code (parameter 4).
    movq %rcx, fiber_restore_reason_code(%rsi)
    #set the restore parameter pointer (parameter 5).
    movq %r8, fiber_restore_param(%rsi)

    #prepare the stack.
    leaq 0x40(%rsp), %rsp

    #indirect jump to context
    jmp *%r9

.size rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_2_fiber_switch,.-rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_2_fiber_switch

# Mark that we don't need executable stack.
.section .note.GNU-stack,"",%progbits
