# How to build

## Prerequisites
- Python 3.11, with llvmlite and pyparsing
- OCaml
- Docker


```zsh
$ make lexer
$ python3.11 main.py
$ docker pull whopper4/group8:clang-riscv
```
and you can see `min-rt.ll` in `samples` directory.
to change the input file, edit `main.py`, i.e. the argument of `main` function.

After that, run `compile.sh`.

To simulate the program, run `sim.sh`.

If you have any issues, please let me know.