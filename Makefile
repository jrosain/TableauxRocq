all: RocqMakefile
	make -f RocqMakefile

RocqMakefile:
	sh devtools/configure.sh

config:
	sh devtools/configure.sh

clean:
	make clean -f RocqMakefile

install:
	make install -f RocqMakefile

doc:
	COQMAKEFILE=RocqMakefile COQDOCJS_DIR=devtools make coqdoc -f RocqMakefile
	sh devtools/make-index.sh
	cp devtools/extra/index.html html/
