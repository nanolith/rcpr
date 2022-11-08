CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
    --object-bits 16 \
	--unwind 10 --unwinding-assertions \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/assertions/prop_valid_range.c \
	../models/shadow/fiber/prop_fiber_valid.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_release.c \
	../models/shadow/uuid/prop_uuid_valid.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../src/uuid/rcpr_uuid_parse_string.c \
	../models/rcpr_uuid_parse_string_main.c
