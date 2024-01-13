
report: log.txt
#	grep DEBUG2B: log.txt | cut -d: -f2  |sort -u
	grep -A1 DEBUG2A: log.txt 

install:
	dune build -p        ppx-introspector -j 23 @install

build1: clean
	dune build

clean :
	dune clean	

log.txt:  src/ppx.ml
	dune clean
	dune build --display=quiet > log.txt 2>&1
