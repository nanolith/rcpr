#Detect kqueue
check_symbol_exists(kqueue "sys/types.h;sys/event.h" HAS_PSOCK_ASYNC_KQUEUE)
check_symbol_exists(epoll_wait "sys/epoll.h" HAS_PSOCK_ASYNC_EPOLL)
check_symbol_exists(select "sys/select.h" HAS_PSOCK_ASYNC_SELECT)

if (PSOCK_ASYNC_USE_SELECT)
    SET(HAS_PSOCK_ASYNC_KQUEUE FALSE)
    SET(HAS_PSOCK_ASYNC_EPOLL FALSE)
endif()

#prefer kqueue first
if (HAS_PSOCK_ASYNC_KQUEUE)
    SET(HAS_PSOCK_ASYNC TRUE)
    FILE(GLOB RCPR_PSOCK_ASYNC_SOURCES src/psock/platform/kqueue/*.c)
#prefer epoll next
elseif (HAS_PSOCK_ASYNC_EPOLL)
    SET(HAS_PSOCK_ASYNC TRUE)
    FILE(GLOB RCPR_PSOCK_ASYNC_SOURCES src/psock/platform/epoll/*.c)
#prefer select last
elseif (HAS_PSOCK_ASYNC_SELECT)
    SET(HAS_PSOCK_ASYNC TRUE)
    FILE(GLOB RCPR_PSOCK_ASYNC_SOURCES src/psock/platform/select/*.c)
else ()
    SET(HAS_PSOCK_ASYNC FALSE)
endif ()
