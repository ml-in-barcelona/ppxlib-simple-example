
report: log.txt
	grep TOPstruc log.txt |fold -w 50 | grep FIXME  |sort |uniq -c |sort -n 

install:
	dune build -p        ppx-introspector -j 23 @install

build1: clean
	dune build

clean :
	dune clean	

log.txt:  src/ppx.ml
	dune clean
	dune build --display=quiet > log.txt 2>&1
