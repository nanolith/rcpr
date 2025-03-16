CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	-I ../include -I ../build/include \
	../src/socket_utilities/socket_utility_socketpair.c \
	../models/shadow/allocator/allocator.c \
	../models/shadow/unistd/close.c \
	../models/shadow/unistd/descriptor.c \
	../models/shadow/unistd/socketpair.c \
	../models/socket_utility_socketpair_main.c
