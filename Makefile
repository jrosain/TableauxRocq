all: RocqMakefile
	make -f RocqMakefile

RocqMakefile:
	bash devtools/configure.sh

config:
	bash devtools/configure.sh

clean:
	make clean -f RocqMakefile
	cd checker && dune clean
	git clean -Xf

install:
	make install -f RocqMakefile

poulet: all
	cd checker && dune build
	rm -f poulet && ln -s checker/_build/default/bin/poulet.exe poulet

doc: RocqMakefile
	COQMAKEFILE=RocqMakefile COQDOCJS_DIR=devtools make coqdoc -f RocqMakefile
	bash devtools/make-index.sh
	cp devtools/extra/index.html html/
