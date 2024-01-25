DOCKER_IMAGE=whopper4/group8:clang-riscv
DIR=$(shell pwd)
PY=python3.11
lexer:
	reflex --header-file lexspec.l
	clang++ -std=c++11 -O2 lex.yy.cpp lex.cpp -o lex -lreflex
	rm -f lex.yy.cpp lex.yy.h
#	ocamllex lexer.mll
#	ocamlfind ocamlc -c pre.ml lexer.ml lex.ml -package base64
#	ocamlfind ocamlc -o lex -package base64 -linkpkg pre.cmo lexer.cmo lex.cmo
#	rm -f lexer.ml

fib:
	$(PY) main.py samples/fib.ml
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ $(DOCKER_IMAGE) bash -c \
	"clang -I/riscv/_install/riscv64-unknown-elf/include -O2 -c fib.ll lib.c --target=riscv32 -march=rv32imafc -mabi=ilp32f && \
	riscv64-unknown-elf-gcc fib.o lib.o -o fib -march=rv32imafc -mabi=ilp32f -lm"

min-rt:
	$(PY) main.py samples/min-rt.ml
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ $(DOCKER_IMAGE) bash -c \
	"clang -I/riscv/_install/riscv64-unknown-elf/include \
	-O2 -c min-rt.ll lib.c --target=riscv32 -march=rv32imafc -mabi=ilp32f && \
	riscv64-unknown-elf-gcc min-rt.o lib.o -o min-rt -march=rv32imafc -mabi=ilp32f -lm && \
	rm -f min-rt.o lib.o"

minrt:
	$(PY) main.py samples/raytracer/minrt.ml
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ $(DOCKER_IMAGE) bash -c \
	"clang -I/riscv/_install/riscv64-unknown-elf/include \
	-O2 -c raytracer/minrt.ll lib.c --target=riscv32 -march=rv32imafc -mabi=ilp32f && \
	riscv64-unknown-elf-gcc raytracer/minrt.o lib.o -o minrt -march=rv32imafc -mabi=ilp32f -lm && \
	rm -f raytracer/minrt.o lib.o"

launch:
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ -it $(DOCKER_IMAGE) bash

test-cls-check:
	for f in test/*.ml; do if ! $(PY) main.py $$f; then break; fi; done; \
	$(PY) main.py test/minrt/globals2.ml test/minrt/minrt.ml; \
	rm -f test/*.knormal.ml test/*.ml.lex

.SILENT: sim
sim:
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ -i $(DOCKER_IMAGE) bash -c \
	"time qemu-riscv32 $(what)"

asm:
	docker run --rm -v "$(DIR)/samples":/usr/src/ -w /usr/src/ $(DOCKER_IMAGE) bash -c \
	"clang -I/riscv/_install/riscv64-unknown-elf/include -O2 -S $(what) lib.c --target=riscv32 -march=rv32imafc -mabi=ilp32f"

.PHONY: clean
clean:
	rm -f *.cmi *.cmo *.ll *.s *.o