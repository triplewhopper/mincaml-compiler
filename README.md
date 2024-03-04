# How to build

## Prerequisites
- Python 3.11
- [RE/flex 3.5.1](https://github.com/Genivia/RE-flex) (for building lexer)
Please ensure that `python3.11` is available. If not, please change the `python3.11` in `Makefile` to `python3` or `python` or whatever you have.


### Building lexer
```zsh
$ make lex
```

### Compile .ml file
```zsh
$ python3.11 main.py -h
usage: main.py [-h] [--version] [-o FILE] [--inline SIZE] [--print-ir] [--print-knormal] [--print-closure] [--print-type] files [files ...]

MinCaml compiler, version 1.0.0

positional arguments:
  files            input files

options:
  -h, --help       show this help message and exit
  --version        show program's version number and exit
  -o FILE          output file. If not specified, the last file is used with the .s extension
  --inline SIZE    max size of function to inline, must be in the range [0, 20]. default 20.
  --print-ir       generate a .ir file for each function, containing the HIR, LIR, and the register allocation result.
  --print-knormal  print the k-normalized program separately for each file
  --print-closure  print the closure-converted program to <last file or '-o'-specified file>.closure.ml
  --print-type     print the type of each function

$ python3.11 main.py test/minrt/globals2.ml test/minrt/minrt.ml -o main.s 
```
### Append the runtime library
```zsh
$ cat runtime/arraymake.asm >> main.s
```
Then you can use simulator to run `main.s`. If simulator reports errors like `label not found: 'print_int'`, try
```zsh
$ cat runtime/misc.asm >> main.s
```
