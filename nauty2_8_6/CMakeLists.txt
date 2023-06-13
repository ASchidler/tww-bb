CHECK_IF_DEBUG()
# file(GLOB_RECURSE NAUTY RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *)
add_library (nauty nauty.c naututil.c naugraph.c schreier.c naurng.c nautinv.c gtools.c nausparse.c nautil.c)

# set_target_properties(nauty PROPERTIES LINKER_LANGUAGE C)
target_include_directories (nauty PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
