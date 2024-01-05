# How to build

## Prerequisites
- Python 3.11, with llvmlite and pyparsing
- OCaml
- Docker


```zsh
$ docker pull whopper4/group8:clang-riscv
$ make lexer
$ make clean
$ make fib
$ make sim what=fib
20
6765

real    0m1.304s
user    0m0.010s
sys     0m0.012s
$ make min-rt
$ cp ?? samples/contest.sld # replace ?? with where you put contest.sld
$ make sim what=min-rt < samples/contest.sld > samples/contest.min-rt.ppm

```

If you have any issues, please let me know.