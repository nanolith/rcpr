##
# \file fiber/platform/sysv/x86_64/fiber_make.s
#
# \brief Set up the stack and context structure for a fiber.
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

#fiber make function
.section text
.globl rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_4_fiber_make
.type fiber_make,@function

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

#fiber_make takes three arguments: the fiber instance, the fiber scheduler,
#and the entry pointer.

.text
.align 16
rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_4_fiber_make:

    # load the stack pointer from the fiber instance.
    movq fiber_stack_ptr(%rdi), %rax

    # shift address in RAX to lower 16 byte boundary.
    andq  $-16, %rax

    # reserve space for context-data on context-stack
    # on context-function entry: (RSP -0x8) % 16 == 0.
    leaq  -0x40(%rax), %rax

    # third arg of fiber_make() == address of context-function
    # stored in RBX.
    movq  %rdx, 0x28(%rax)

    # first arg of fiber_make() == address of fiber, stored in R15.
    movq  %rdi, 0x20(%rax)

    # second arg of fiber_make() == address of scheduler, stored in R14
    movq  %rsi, 0x18(%rax)

    # save MMX control- and status-word.
    stmxcsr  (%rax)
    # save x87 control-word.
    fnstcw   0x4(%rax)

    # compute abs address of label trampoline.
    leaq  trampoline(%rip), %rcx
    # save address of trampoline as return-address for the context-function
    # will be entered after calling jump_fcontext() for the first time.
    movq  %rcx, 0x38(%rax)

    # compute abs address of label finish.
    leaq  finish(%rip), %rcx
    # save address of finish as return-address for context-function
    # will be entered after context-function returns.
    movq  %rcx, 0x30(%rax)

    #save the stack pointer.
    movq  %rax, fiber_stack_ptr(%rdi)

    #return
    ret

trampoline:
    # the first parameter to the entry function is saved in R14
    movq  %r14, %rdi
    # the second parameter to the entry function is saved in R15.
    movq  %r15, %rsi

    # store return address on stack.
    # fix stack alignment.
    push %rbp
    # jump to context-function.
    jmp *%rbx

finish:
    # exit code is non-zero.
    mov 0x1, %rdi
    # exit application.
    call  _exit@PLT
    hlt

.size rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_4_fiber_make,.-rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_4_fiber_make

# Mark that we don't need executable stack.
.section .note.GNU-stack,"",%progbits
