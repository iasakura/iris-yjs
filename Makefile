all: Makefile.coq
	+make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
.PHONY: clean

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq
