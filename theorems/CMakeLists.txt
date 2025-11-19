FILE(GLOB_RECURSE ROCQ_RCPR_SOURCES RCPR/*.v)

FOREACH(source ${ROCQ_RCPR_SOURCES})
    STRING(REPLACE "${CMAKE_CURRENT_SOURCE_DIR}/" "" relative_path ${source})
    STRING(REPLACE "/" "_" TARGET_NAME "build_rocq_${relative_path}")

    MESSAGE(INFO, "Added target ${TARGET_NAME}")

    ADD_CUSTOM_COMMAND(
        OUTPUT ${source}o
        COMMAND coqc -R ${CMAKE_CURRENT_SOURCE_DIR}/RCPR RCPR ${source}
        DEPENDS ${source})

    ADD_CUSTOM_TARGET(
        ${TARGET_NAME} ALL
        DEPENDS ${source}o)
ENDFOREACH()

# dependencies
add_dependencies(
    build_rocq_RCPR_Data_IList.v
    build_rocq_RCPR_Data_Maybe.v)

add_dependencies(
    build_rocq_RCPR_Data_Monoid.v
    build_rocq_RCPR_Data_Semigroup.v)

add_dependencies(
    build_rocq_RCPR_Theorems_Semigroup.v
    build_rocq_RCPR_Data_Semigroup.v)

add_dependencies(
    build_rocq_RCPR_Theorems_Monoid.v
    build_rocq_RCPR_Data_Monoid.v)
