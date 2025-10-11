if [ -f RocqMakefile ]; then
    make mrproper
fi

rocq makefile -f _RocqProject -o RocqMakefile
