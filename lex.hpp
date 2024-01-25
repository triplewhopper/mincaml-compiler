#pragma once
#include <iostream>
#include <fstream>
#include <algorithm>

struct Triple{
    static bool no_cnum;
    size_t cnum;
    size_t lineno;
    size_t colno;
    size_t end_lineno;
    size_t end_colno;
    std::string text;
};

struct Op : Triple{
    Op(size_t cnum, size_t lineno, size_t colno, size_t end_lineno, size_t end_colno, std::string &&text): 
        Triple{cnum, lineno, colno, end_lineno, end_colno, std::move(text)} {}
};
struct I: Triple{
    I(size_t cnum, size_t lineno, size_t colno, size_t end_lineno, size_t end_colno, std::string &&text): 
        Triple{cnum, lineno, colno, end_lineno, end_colno, std::move(text)} {}
};
struct F: Triple{
    F(size_t cnum, size_t lineno, size_t colno, size_t end_lineno, size_t end_colno, std::string &&text): 
        Triple{cnum, lineno, colno, end_lineno, end_colno, std::move(text)} {}
};
struct B: Triple{
    B(size_t cnum, size_t lineno, size_t colno, size_t end_lineno, size_t end_colno, std::string &&text): 
        Triple{cnum, lineno, colno, end_lineno, end_colno, std::move(text)} {}
};
struct W: Triple{
    W(size_t cnum, size_t lineno, size_t colno, size_t end_lineno, size_t end_colno, std::string &&text): 
        Triple{cnum, lineno, colno, end_lineno, end_colno, std::move(text)} {}
};
struct Eof: Triple{
    explicit Eof(size_t cnum, size_t lineno, size_t colno): 
        Triple{cnum, lineno, colno, lineno, colno, "EOF"} {}
};
#define MAKE_OUT(kind, cls) \
    inline std::ostream& operator<<(std::ostream& os, const cls& v) { \
        if (!Triple::no_cnum) os << v.cnum << ' '; \
        os << v.lineno << ' ' << v.colno << ' ' << v.end_lineno << ' ' << v.end_colno << ' '; \
        os << #kind << ' ' << v.text; \
        return os; \
    }
MAKE_OUT(Op, Op)
MAKE_OUT(I, I)
MAKE_OUT(F, F)
MAKE_OUT(B, B)
MAKE_OUT(W, W)
MAKE_OUT(EOF, Eof)
#undef MAKE_OUT
