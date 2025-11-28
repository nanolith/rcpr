FILE(GLOB_RECURSE ROCQ_RCPR_SOURCES *.v)

FOREACH(source ${ROCQ_RCPR_SOURCES})
    STRING(REPLACE "${CMAKE_CURRENT_SOURCE_DIR}/" "" relative_path ${source})
    STRING(REPLACE "/" "_" TARGET_NAME "build_rocq_${relative_path}")

    MESSAGE(INFO, "Added target ${TARGET_NAME}")

    ADD_CUSTOM_COMMAND(
        OUTPUT ${source}o
        COMMAND coqc
            -R ${CMAKE_CURRENT_SOURCE_DIR}/RCPR RCPR
            -R ${CMAKE_CURRENT_SOURCE_DIR}/list list ${source}
        DEPENDS ${source})

    ADD_CUSTOM_TARGET(
        ${TARGET_NAME} ALL
        DEPENDS ${source}o)

    if (NOT "${TARGET_NAME}" STREQUAL "build_rocq_RCPR_Helpers_Notation.v")
        add_dependencies(
            ${TARGET_NAME}
            build_rocq_RCPR_Helpers_Notation.v)
    endif()

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
    build_rocq_RCPR_Data_Monoid.v
    build_rocq_RCPR_Data_Semigroup.v)

add_dependencies(
    build_rocq_RCPR_Data_Applicative.v
    build_rocq_RCPR_Data_Functor.v)

add_dependencies(
    build_rocq_RCPR_Theorems_Applicative.v
    build_rocq_RCPR_Data_Applicative.v)

add_dependencies(
    build_rocq_RCPR_Theorems_Functor.v
    build_rocq_RCPR_Data_Functor.v)

add_dependencies(
    build_rocq_RCPR_Data_Either.v
    build_rocq_RCPR_Data_Applicative.v
    build_rocq_RCPR_Data_Monad.v)

add_dependencies(
    build_rocq_RCPR_Data_Monad.v
    build_rocq_RCPR_Data_Applicative.v)

add_dependencies(
    build_rocq_RCPR_Theorems_Monad.v
    build_rocq_RCPR_Data_Applicative.v
    build_rocq_RCPR_Data_Monad.v)

add_dependencies(
    build_rocq_list_CMachine.v
    build_rocq_RCPR_Data_Applicative.v
    build_rocq_RCPR_Data_Functor.v
    build_rocq_RCPR_Data_IList.v
    build_rocq_RCPR_Data_Maybe.v
    build_rocq_RCPR_Data_Monad.v
    build_rocq_RCPR_Helpers_Notation.v
    build_rocq_RCPR_Tactics_FunctionalExtensionality.v)

add_dependencies(
    build_rocq_list_CMachineTheorems.v
    build_rocq_list_CMachine.v
    build_rocq_RCPR_Data_Applicative.v
    build_rocq_RCPR_Data_Functor.v
    build_rocq_RCPR_Data_IList.v
    build_rocq_RCPR_Data_Maybe.v
    build_rocq_RCPR_Data_Monad.v
    build_rocq_RCPR_Helpers_Notation.v)

#add_dependencies(
#    build_rocq_list_heap.v
#    build_rocq_RCPR_Data_Applicative.v
#    build_rocq_RCPR_Data_Either.v
#    build_rocq_RCPR_Data_Functor.v
#    build_rocq_RCPR_Data_IList.v
#    build_rocq_RCPR_Data_Maybe.v
#    build_rocq_RCPR_Data_Monad.v
#    build_rocq_RCPR_Tactics_FunctionalExtensionality.v)
