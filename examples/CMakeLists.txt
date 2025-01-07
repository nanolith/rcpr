ADD_SUBDIRECTORY(mandelbrot)

if (RCPR_FIBER_FOUND)
    ADD_SUBDIRECTORY(echo_server)
    ADD_SUBDIRECTORY(http_server)
endif()
