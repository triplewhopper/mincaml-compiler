#!/bin/zsh
input="contest.sld"
output="contest.min-rt.ppm"
docker run --rm -v "$PWD/samples":/usr/src/ -w /usr/src/ clang-riscv bash -c \
"time qemu-riscv32 min-rt < $input > $output"