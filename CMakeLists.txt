cmake_minimum_required (VERSION 2.6)
project (PW3)
 
add_library(err err.c)
add_executable (circuit circuit.c)
target_link_libraries (circuit err)
