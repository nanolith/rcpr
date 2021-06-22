#Initially, fibers haven't been detected.
SET(RCPR_FIBER_FOUND FALSE)

#Detect fiber processor
if ("${CMAKE_SYSTEM_PROCESSOR}" MATCHES "amd64")
    SET(RCPR_FIBER_PROCESSOR "x86_64")
elseif ("${CMAKE_SYSTEM_PROCESSOR}" MATCHES "x86_64")
    SET(RCPR_FIBER_PROCESSOR "x86_64")
else ()
    SET(RCPR_FIBER_PROCESSOR "invalid")
endif ()

#Detect fiber ABI
if ("${CMAKE_SYSTEM_NAME}" MATCHES "Linux")
    SET(RCPR_FIBER_ABI "sysv")
elseif ("${CMAKE_SYSTEM_NAME}" MATCHES "FreeBSD")
    SET(RCPR_FIBER_ABI "sysv")
elseif ("${CMAKE_SYSTEM_NAME}" MATCHES "NetBSD")
    SET(RCPR_FIBER_ABI "sysv")
elseif ("${CMAKE_SYSTEM_NAME}" MATCHES "OpenBSD")
    SET(RCPR_FIBER_ABI "sysv")
else ()
    SET(RCPR_FIBER_ABI "invalid")
endif ()

#fiber assembler options
SET(RCPR_FIBER_PLATFORM "${RCPR_FIBER_PROCESSOR}-${RCPR_FIBER_ABI}")
if ("${RCPR_FIBER_PLATFORM}" MATCHES "x86_64-sysv")
    SET(CMAKE_ASM_COMPILER ${CMAKE_C_COMPILER})
    enable_language(ASM)
    include_directories("src/fiber/platform/sysv/x86_64")
    SET(RCPR_FIBER_FOUND TRUE)
    FILE(GLOB RCPR_FIBER_SYSV_X86_64_SOURCES src/fiber/platform/sysv/x86_64/*.s)
    SET(RCPR_FIBER_PLATFORM_SOURCES ${RCPR_FIBER_SYSV_X86_64_SOURCES})
    set_source_files_properties(
        ${RCPR_FIBER_SYSV_X86_64_SOURCES} PROPERTIES
        COMPILE_FLAGS "-I${CMAKE_SOURCE_DIR}/src/fiber/platform/sysv/x86_64")
else ()
    if ("${RCPR_FIBER_PROCESSOR}" MATCHES "invalid")
        message(
            WARNING "Fibers not supported on cpu ${CMAKE_SYSTEM_PROCESSOR}.")
    elseif ("${RCPR_FIBER_ABI}" MATCHES "invalid")
        message(WARNING "Fibers not supported on OS ${CMAKE_SYSTEM_NAME}.")
    endif ()
endif ()
