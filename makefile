.PHONY: all clean

-include makefile.coq

all: makefile.coq
	make -f "$?"

makefile.coq: _CoqProject
	coq_makefile -f "$?" -o "$@"
