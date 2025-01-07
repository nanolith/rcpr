#Detect kqueue
include ("cmake/fibers.cmake")

if (RCPR_FIBER_FOUND)
    check_symbol_exists(kqueue "sys/types.h;sys/event.h" HAS_PSOCK_ASYNC_KQUEUE)
    check_symbol_exists(epoll_wait "sys/epoll.h" HAS_PSOCK_ASYNC_EPOLL)
    check_symbol_exists(poll "sys/poll.h" HAS_PSOCK_ASYNC_POLL)

    if (PSOCK_ASYNC_USE_POLL)
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
    elseif (HAS_PSOCK_ASYNC_POLL)
        SET(HAS_PSOCK_ASYNC TRUE)
        FILE(GLOB RCPR_PSOCK_ASYNC_SOURCES src/psock/platform/poll/*.c)
    else ()
        SET(HAS_PSOCK_ASYNC FALSE)
    endif ()
else ()
    SET(HAS_PSOCK_ASYNC FALSE)
endif ()
