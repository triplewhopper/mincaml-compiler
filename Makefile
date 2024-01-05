DOCKER_IMAGE=whopper4/group8:clang-riscv
DIR=$(shell pwd)
PY=python3.11
lexer: 
	ocamllex lexer.mll
	ocamlfind ocamlc -c pre.ml lexer.ml lex.ml -package base64
	ocamlfind ocamlc -o lex -package base64 -linkpkg pre.cmo lexer.cmo lex.cmo 
	rm -f lexer.ml

fib:
	$(PY) main.py samples/fib.ml
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ $(DOCKER_IMAGE) bash -c \
	"clang -I/riscv/_install/riscv64-unknown-elf/include -O2 -c fib.ll lib.c --target=riscv32 && \
	riscv64-unknown-elf-gcc fib.o lib.o -o fib -march=rv32i -mabi=ilp32 -lm"

min-rt:
	$(PY) main.py samples/min-rt.ml
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ $(DOCKER_IMAGE) bash -c \
	"clang -I/riscv/_install/riscv64-unknown-elf/include -O2 -c min-rt.ll lib.c --target=riscv32 && \
	riscv64-unknown-elf-gcc min-rt.o lib.o -o min-rt -march=rv32i -mabi=ilp32 -lm"

sim:
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ -i $(DOCKER_IMAGE) bash -c \
	"time qemu-riscv32 $(what)"


.PHONY: clean
clean:
	rm -f *.cmi *.cmo fib min-rt *.ll *.s *.o