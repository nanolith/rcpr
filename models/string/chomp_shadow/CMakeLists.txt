SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/models/shadow/string/chomp.c
    main.c)

ADD_EXECUTABLE(model_string_chomp_shadow ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_string_chomp_shadow PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_string_chomp_shadow
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_string_chomp_shadow
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_string_chomp_shadow
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_string_chomp_shadow
    USES_TERMINAL)
