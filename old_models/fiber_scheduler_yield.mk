CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
    --unwindset resource_release:1,fiber_scheduler_resource_release:1 \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/fiber/prop_fiber_valid.c \
	../models/shadow/fiber/fiber_struct_tag_init.c \
	../models/shadow/fiber/prop_fiber_scheduler_valid.c \
	../models/shadow/fiber/fiber_scheduler_struct_tag_init.c \
	../models/shadow/fiber/fiber_create_for_thread.c \
	../models/shadow/fiber/fiber_resource_release.c \
	../models/shadow/fiber/fiber_switch.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_release.c \
	../models/shadow/stack/prop_stack_valid.c \
	../models/shadow/stack/stack_struct_tag_init.c \
	../models/shadow/unistd/mmap_for_stack.c \
	../models/shadow/unistd/munmap.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/fiber/common/fiber_resource_handle.c \
	../src/fiber/common/fiber_scheduler_yield.c \
	../src/fiber/common/fiber_scheduler_create.c \
	../src/fiber/common/fiber_scheduler_resource_handle.c \
	../src/fiber/common/fiber_scheduler_resource_release.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../src/stack/stack_resource_handle.c \
	../models/fiber_scheduler_yield_main.c
