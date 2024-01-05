#!/bin/zsh
srcs="min-rt.ll lib.c"
objs="min-rt.o lib.o"
exe="min-rt"
docker run --rm -v "$PWD/samples":/usr/src/ -w /usr/src/ whopper4/group8:clang-riscv bash -c \
"clang -I/riscv/_install/riscv64-unknown-elf/include -O2 -c $srcs --target=riscv32 &&
riscv64-unknown-elf-gcc $objs -o $exe -march=rv32i -mabi=ilp32 -lm"