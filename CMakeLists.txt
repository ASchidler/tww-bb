cmake_minimum_required(VERSION 3.16)
project(tww-bb)

set(CMAKE_CXX_STANDARD 14)

macro (CHECK_IF_DEBUG)
    if (CMAKE_BUILD_TYPE MATCHES Debug)
        set (CMAKE_BUILD_TYPE Release)
    endif()
endmacro()

add_subdirectory("nauty2_8_6")
find_package(Boost REQUIRED)
find_package(BZip2 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

#set (CMAKE_BUILD_TYPE Release)

SET(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -O3")
add_executable(tww-bb main.cpp graph.h tww.h tools.h twwbb2.h
        lower_bounds.h
        upper_bounds.h twwbb2.cpp BbParameters.cpp BbParameters.h MemoryAwareCache.h LowerBoundGraph.cpp LowerBoundGraph.h
        tools.cpp)
target_link_libraries (tww-bb LINK_PUBLIC bz2 nauty)
