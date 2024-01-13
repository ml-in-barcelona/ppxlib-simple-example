
report: log.txt
	grep DEBUG2B: log.txt | cut -d: -f2- 
	grep DEBUG2A: log.txt | cut -d: -f2-

install:
	dune build -p        ppx-introspector -j 23 @install

build1: clean
	dune build

clean :
	dune clean	

log.txt:  src/ppx.ml
	dune clean
	dune build --display=quiet > log.txt 2>&1
