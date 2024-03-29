CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/psock/prop_psock_valid.c \
	../models/shadow/psock/psock_struct_tag_init.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/unistd/close.c \
	../models/shadow/unistd/descriptor.c \
	../models/shadow/unistd/socketpair.c \
    ../models/shadow/unistd/getsockopt.c \
	../models/shadow/valid_range.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/psock/psock_create_from_descriptor.c \
	../src/psock/psock_resource_handle.c \
	../src/psock/psock_from_descriptor_read.c \
	../src/psock/psock_from_descriptor_write.c \
    ../src/psock/psock_from_descriptor_release.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../src/socket_utilities/socket_utility_socketpair.c \
	../models/psock_create_from_descriptor_main.c
