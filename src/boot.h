/*
 * This header file is included by Cxx.jl upon starting up and provides some basic definitions
 * for functionality provided by Cxx, including interaction with julia functions and expressions.
 */

// For old C libraries that still look at this in C++ mode
#define __STDC_LIMIT_MACROS
#define __STDC_CONSTANT_MACROS

#include <stdint.h>
#include <stddef.h>
#include <cstring>

extern "C" {
    // Usually this is added by the linker, but we just do it ourselves, because we
    // never actually go to the linker.
    void __dso_handle() {}
}
