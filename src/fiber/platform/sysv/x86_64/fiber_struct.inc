##
# \file fiber/platform/sysv/x86_64/fiber_struct.s
#
# \brief Data structures used by the fiber assembler routines.
#
# \copyright 2021 Justin Handville.  Please see license.txt in this
# distribution for the license terms under which this software is distributed.

#define structure for fiber
.section absolute
    .struct 0
fiber_resource_release:
    .struct fiber_resource_release + 8
fiber_stack_ptr:
    .struct fiber_stack_ptr + 8
fiber_allocator_ptr:
    .struct fiber_allocator_ptr + 8
fiber_stack_struct_ptr:
    .struct fiber_stack_struct_ptr + 8
fiber_context_ptr:
    .struct fiber_context_ptr + 8
fiber_user_function_ptr:
    .struct fiber_user_function_ptr + 8
fiber_user_function_context_ptr:
    .struct fiber_user_function_context_ptr + 8
fiber_unexpected_event_ptr:
    .struct fiber_unexpected_event_ptr + 8;
fiber_restore_discipline_id:
    .struct fiber_restore_discipline_id + 8
fiber_restore_reason_code:
    .struct fiber_restore_reason_code + 8
fiber_restore_param:
