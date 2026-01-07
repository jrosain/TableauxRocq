if [ -f RocqMakefile ]; then
	make cleanall -f RocqMakefile
	rm RocqMakefile.conf RocqMakefile
fi

rocq makefile -f _RocqProject -o RocqMakefile
