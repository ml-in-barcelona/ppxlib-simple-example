build1: clean
	dune build

clean :
	dune clean	

log.txt:  src/ppx.ml
	dune clean
	dune build > log.txt 2>&1
