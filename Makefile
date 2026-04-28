all: RocqMakefile
	make -f RocqMakefile

RocqMakefile:
	bash devtools/configure.sh

config:
	bash devtools/configure.sh

clean:
	make clean -f RocqMakefile

install:
	make install -f RocqMakefile

doc: RocqMakefile
	COQMAKEFILE=RocqMakefile COQDOCJS_DIR=devtools make coqdoc -f RocqMakefile
	bash devtools/make-index.sh
	cp devtools/extra/index.html html/
