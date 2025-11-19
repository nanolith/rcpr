FILE(GLOB_RECURSE ROCQ_RCPR_SOURCES RCPR/*.v)

FOREACH(source ${ROCQ_RCPR_SOURCES})
    STRING(REPLACE "/" "_" TARGET_NAME "build_rocq_rcpr_${source}")

    ADD_CUSTOM_COMMAND(
        OUTPUT ${source}o
        COMMAND coqc -R ${CMAKE_CURRENT_SOURCE_DIR}/RCPR RCPR ${source}
        DEPENDS ${source})

    ADD_CUSTOM_TARGET(
        ${TARGET_NAME} ALL
        DEPENDS ${source}o)
ENDFOREACH()
