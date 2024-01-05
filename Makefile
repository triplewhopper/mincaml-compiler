
lexer: 
	ocamllex lexer.mll
	ocamlfind ocamlc -c pre.ml lexer.ml lex.ml -package base64
	ocamlfind ocamlc -o lex -package base64 -linkpkg pre.cmo lexer.cmo lex.cmo 
	rm -f lexer.ml
.PHONY: clean
clean:
	rm -f *.cmi *.cmo